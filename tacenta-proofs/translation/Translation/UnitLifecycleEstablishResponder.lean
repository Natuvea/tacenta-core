import Translation.UnitLifecycleEstablishInitiatorShape
import Translation.SessionUnitDecodeEc
import Translation.UnitLifecycleEstablishedDecrypt

/-!
# `establish_responder` over every input: outcomes, effects, and the inner receive refined

The responder's public root `establish_responder` decodes the initial message, looks up the prekeys it
names, computes the shared secret, checks the last-resort replay record, builds a session, and only then
runs `decrypt_ratchet` on the ratchet frame the message carries; on success it commits the prekey store.
This module composes that root for every responder identity, prekey store, initial message and source of
randomness (category 2 of the maintainer's increment rule), and derives the hypotheses of the
`decrypt_ratchet` refinement at the session it builds (category 1: from the actual construction, not
assumed).  No concrete input is chosen in the generic results.

## What is shown

* `establish_responder_cases` (no hypothesis): every return is one of three outcomes.  (1) A refusal before
  the inner receive, with one of the errors `PrepareRefusal` lists (each helper's refusals are proved:
  `signed_prekey_err` ... `replay_err`), the store and the source of randomness returned as given and no
  session.  (2) An inner refusal of `decrypt_ratchet` on `p.session` and `p.message`, for parts
  `p : ResponderPreparedParts` read off the generated function: its error, the store as given, the source
  `decrypt_ratchet` returned.  (3) An inner success: its plaintext and session, the store after
  `ResponderCommit`, the source `decrypt_ratchet` returned.
* `establish_responder_at_parts` (no hypothesis): when parts exist, the call is exactly the inner receive
  followed by the commit, so such an input is never refused before the inner receive.
* `responderCommit_effects` (under `DerivedKeysModel`), `replay_ok`: what the success commit does.  Every
  field of the store but the one-time curve prekeys, the one-time KEM prekeys and the replay record is
  unchanged; the one-time KEM prekeys are unchanged on the last-resort path; the one-time curve prekeys are
  unchanged when the message names none; the replay record is unchanged on the one-time path and gains
  exactly `(kem_id, fp)` at its end on the last-resort path, `fp` being `last_resort_fingerprint` of the
  shared secret.  Which entry the two removals take is not stated.
* The intermediate session: `responder_prepared_invariant` (`Session::invariant`, under the assumed law
  `DhPublicValid`, the recorded `OptionEqU64Shape`, the value law `DivCeilValue` and the length bound
  `HeaderLenTotal`), `counterHeadroom_responder_prepared` (all four ceilings, no hypothesis: clock 0, sparse
  epoch 0, both chain counters 0, Braid epoch 1), `sessionRefines_responder_prepared` (the relation to
  `responderModelOf dh p`, whose Braid is the model's initial responder state `Model.Braid.initBob` of the
  secret `Braid::responder` was given, by `UnitSatisfiabilityBraidStates.responder_refines`; every other
  field is an equation through the abstraction functions).  `honestChunk_responder_iff` says what
  `HonestChunk` asks there: that a header chunk of epoch 1 comes from a 96-byte message.
* `responder_prepared_decrypt_refines`, `establish_responder_refines`: the `decrypt_ratchet` refinement
  applies to the inner call, so on top of the three outcomes the inner step's result, successor and draws
  refine `Model.Lifecycle.decryptRatchet` at `responderModelOf dh p`; with `decryptRatchet_oracle`, an inner
  refusal leaves the draws unchanged or one shorter and an inner success takes exactly one.
* Non-vacuity.  `establish_responder_returns`: the call returns for every input under the T1 contracts and their
  store bound.
  `establish_responder_short_message_refused` (no hypothesis, every prekey store),
  `establish_responder_unknown_prekey_refused` (no hypothesis, every store of a stated shape) and
  `establish_responder_legacy_refused` (the zeroizing round trip, every store of a stated shape): those
  refusals are returned, each with the store and the source as given, at every store they quantify over; no store
  value is derivable in Lean without `ResponderSuccessShape`.  `establish_responder_noncontributory_refused`,
  `establish_responder_replay_refused`, `establish_responder_record_full_refused` (the T1 contracts,
  `ResponderSuccessShape`, and for the first `ZeroKeyShape`): those refusals are reached at an exhibited store.
  `responder_prepared_inhabited`: an input reaching the inner receive exists.
  `responder_route_hypotheses_jointly_satisfiable`: every premise of `establish_responder_refines` holds
  together at an input that reaches the inner receive (`ResponderRouteHypotheses`), under the decrypt laws,
  the responder contract axioms, `ResponderSuccessShape` and `DhPublicValid`;
  `responder_route_inner_refusal_reachable`: there, with `ZeroKeyShape`, the call returns the inner refusal
  mapping to the model's `NonContributoryAgreement`; `responder_route_laws_model`: those laws and both shapes
  hold together in one interpretation, `Interp.modelEstablished`.

Six trivial byte-list lemmas (`wireKey_length` ... `ephKey_key`) are proved with `simp`, which uses `propext`,
rather than by `decide`, which uses no axiom: `attest.py`'s pin reader reads only the form "depends on axioms:
[...]" and not "does not depend on any axioms".  That is a limit of the tool, not a change to what the
results trust.

## What it does not show

* A success of the whole call: no input is exhibited at which the inner `decrypt_ratchet` succeeds
  (`establish_responder_at_parts` makes the condition exact).  Honest successes are tested only
  (`tacenta-core/tests/full_session.rs` and the other responder tests).
* The refusals `BadEncoding` (not reachable after `decode_initial` accepted, by reading
  `tacenta-core/wire/src/lib.rs`; not checked in Lean), `Handshake(InvalidIdentityKey)` and `Kem` are not shown
  reached: the joint model's prime-order check and KEM decapsulation accept every input.
* That `responderModelOf dh p` is the session `Model.Lifecycle.prepareResponder` builds, that the refusal
  reasons before the inner receive are the model's, or the model's `establishResponder` equality: the
  responder establishment T3 is not here.
* Anything about the initiator's frame, the plaintext, the successor's invariant or the responder's next
  operation.
* The run's chunk relation, `HonestChunk`, the trace equation and the draw: the caller's, asked of the parts
  the call reaches the inner receive with; an attacker chooses the chunk.
* That the real primitives meet `DhPublicValid`, `OptionEqU64Shape`, `DivCeilValue`, the decrypt boundary
  records, `ResponderSuccessShape` or `ZeroKeyShape`: assumed, each with a model.  A source with no state of
  its own, such as `OsRng`, is outside every statement about draws.
-/

namespace Tacenta.UnitLifecycleEstablishResponder

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv bind2_eq_ok_inv bind3_eq_ok_inv)

/-- The `Zeroize` instance of a 32-byte array, as the generated code spells it. -/
noncomputable abbrev z32 : zeroize.Zeroize (Array U8 32#usize) :=
  Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)

/-- The full-range slice of a 32-byte array, as the generated code takes it. -/
noncomputable abbrev fullSlice (a : Array U8 32#usize) : Result (Slice U8) :=
  core.array.Array.index
    (core.ops.index.IndexSlice (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice U8)) a ()

/-- The pieces `establish_responder` assembles the session it hands to `decrypt_ratchet` from, with every
fact the code checked or computed on the way.  Every field is read off the generated function; none is
assumed.  Two values are computed twice by the code and appear twice here: the signed prekey's private key
(`signedPrekey`, used for the agreements and the Triple's sending key, and `ratchetPrivate`, stored in the
session) and the shared secret's slice (`tripleSecret`, `braidSecret`). -/
structure ResponderPreparedParts (our : lifecycle.Identity) (store : lifecycle.PrekeyStore)
    (msg : Slice U8) where
  decoded : tacenta_wire.DecodedInitial
  signedSecret : zeroize.Zeroizing (Array U8 32#usize)
  kemSlot : lifecycle.KemKeySlot
  lastResort : Bool
  peerIdentity : tacenta_boundary.dh.PublicKeyBytes
  peerEphemeral : tacenta_boundary.dh.PublicKeyBytes
  oneTime : Option tacenta_boundary.dh.PrivateKey
  kemSecret : Array U8 32#usize
  kemSecretZ : zeroize.Zeroizing (Array U8 32#usize)
  signedBytes : Array U8 32#usize
  signedPrekey : tacenta_boundary.dh.PrivateKey
  shared : Array U8 32#usize
  secretZ : zeroize.Zeroizing (Array U8 32#usize)
  secret : Array U8 32#usize
  replay : Option (Array U8 32#usize)
  tripleSecret : Slice U8
  ratchetPublic : tacenta_boundary.dh.PublicKeyBytes
  ratchetBytes : Array U8 32#usize
  triple : tacenta_triple.State
  braidSecret : Slice U8
  braid : tacenta_braid.Braid
  ratchetPrivate : tacenta_boundary.dh.PrivateKey
  ourPublic : tacenta_boundary.dh.PublicKeyBytes
  identityAd : alloc.vec.Vec U8
  ephemeralCopy : alloc.vec.Vec U8
  hDecode : tacenta_wire.decode_initial msg = ok (core.result.Result.Ok decoded)
  hSigned : lifecycle.responder_signed_prekey_secret store decoded.signed_prekey_id =
    ok (core.result.Result.Ok signedSecret)
  hSlot : lifecycle.responder_kem_slot store decoded.kem_prekey_id =
    ok (core.result.Result.Ok (kemSlot, lastResort))
  hCurve : lifecycle.responder_curve_inputs decoded.identity.deref decoded.ephemeral.deref =
    ok (core.result.Result.Ok (peerIdentity, peerEphemeral))
  hOneTime : lifecycle.responder_one_time_key store decoded.one_time_prekey_id =
    ok (core.result.Result.Ok oneTime)
  hDecaps : lifecycle.responder_decapsulate store kemSlot decoded.kem_ciphertext.deref =
    ok (core.result.Result.Ok kemSecret)
  hKemSecretZ : zeroize.Zeroizing.new z32 kemSecret = ok kemSecretZ
  hSignedBytes : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 signedSecret = ok signedBytes
  hSignedPrekey : tacenta_boundary.dh.PrivateKey.from_bytes signedBytes = ok signedPrekey
  hShared : ∃ (identityKey : tacenta_boundary.dh.PrivateKey) (encapsulated : Array U8 32#usize),
    lifecycle.Identity.dh_key our = ok identityKey ∧
    zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 kemSecretZ = ok encapsulated ∧
    responder_shared_secret identityKey signedPrekey oneTime peerIdentity peerEphemeral encapsulated =
      ok (core.result.Result.Ok shared)
  hSecretZ : zeroize.Zeroizing.new z32 shared = ok secretZ
  hSecret : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 secretZ = ok secret
  hReplay : lifecycle.responder_replay_fingerprint store decoded.kem_prekey_id secret lastResort =
    ok (core.result.Result.Ok replay)
  hTripleSecret : fullSlice secret = ok tripleSecret
  hRatchetPublic : tacenta_boundary.dh.PrivateKey.public_key signedPrekey = ok ratchetPublic
  hRatchetBytes : tacenta_boundary.dh.PublicKeyBytes.as_bytes ratchetPublic = ok ratchetBytes
  hTriple : tacenta_triple.State.init_receiver tripleSecret ratchetBytes tacenta_ratchet.LabelSet.Tacenta =
    ok triple
  hBraidSecret : fullSlice secret = ok braidSecret
  hBraid : tacenta_braid.Braid.responder braidSecret = ok braid
  hRatchetPrivate : tacenta_boundary.dh.PrivateKey.from_bytes signedBytes = ok ratchetPrivate
  hOurPublic : lifecycle.Identity.public our = ok ourPublic
  hIdentityAd : lifecycle.identity_ad peerIdentity ourPublic = ok identityAd
  hEphemeralCopy : alloc.vec.CloneVec.clone core.clone.CloneU8 decoded.ephemeral = ok ephemeralCopy

variable {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8}

/-- The session `establish_responder` passes to `decrypt_ratchet`, field for field as the code builds it. -/
def ResponderPreparedParts.session (p : ResponderPreparedParts our store msg) : lifecycle.Session :=
  { triple := p.triple, braid := p.braid, ratchet_private := p.ratchetPrivate,
    identity_ad := p.identityAd, our_identity_public := p.ourPublic,
    peer_identity_public := p.peerIdentity, pending_initial := none,
    established_ephemeral := some p.ephemeralCopy }

/-- The ratchet frame `establish_responder` passes to `decrypt_ratchet`: the initial message's tail. -/
def ResponderPreparedParts.message (p : ResponderPreparedParts our store msg) : Slice U8 :=
  p.decoded.message.deref

/-- What a successful `establish_responder` does to the prekey store, step for step as the code does it
after the inner receive succeeded: the one-time KEM prekey the message named is taken unless the KEM key
is a last-resort key, then the one-time curve prekey is taken if the message named one, then on the
last-resort path the replay record gains the fingerprint, after the code's assertion that the key's count
is below the bound. -/
def ResponderCommit (store : lifecycle.PrekeyStore) (kemId oneTimeId : U32) (lastResort : Bool)
    (replay : Option (Array U8 32#usize)) (store' : lifecycle.PrekeyStore) : Prop :=
  ∃ store1 store2,
    (if lastResort then store1 = store
      else ∃ x, lifecycle.PrekeyStore.take_one_time_kem store kemId = ok (x, store1)) ∧
    (if oneTimeId != serialization.ABSENT_ID
      then ∃ b, lifecycle.PrekeyStore.take_one_time store1 oneTimeId = ok (b, store2)
      else store2 = store1) ∧
    (match replay with
      | none => store' = store2
      | some fp => ∃ count seen,
          lifecycle.PrekeyStore.last_resort_seen_for store2 kemId = ok count ∧
          count < lifecycle.MAX_LAST_RESORT_SEEN ∧
          alloc.vec.Vec.push store2.last_resort_seen (kemId, fp) = ok seen ∧
          store' = { store2 with last_resort_seen := seen })

/-- The refusals `establish_responder` can return before it decrypts, by the helper that returns each. -/
def PrepareRefusal (e : lifecycle.Error) : Prop :=
  (∃ d, e = lifecycle.Error.Decode d) ∨ e = lifecycle.Error.UnknownPrekeyId ∨
    e = lifecycle.Error.LegacyLastResortRecord ∨ e = lifecycle.Error.BadEncoding ∨
    e = lifecycle.Error.Handshake SessionError.InvalidIdentityKey ∨
    e = lifecycle.Error.Handshake SessionError.NonContributoryAgreement ∨
    e = lifecycle.Error.Kem ∨ e = lifecycle.Error.ReplayedLastResort ∨
    e = lifecycle.Error.LastResortRecordFull

/-- `responder_signed_prekey_secret` refuses only with `UnknownPrekeyId`. -/
theorem signed_prekey_err (store : lifecycle.PrekeyStore) (id : U32) (e : lifecycle.Error)
    (h : lifecycle.responder_signed_prekey_secret store id = ok (core.result.Result.Err e)) :
    e = lifecycle.Error.UnknownPrekeyId := by
  unfold lifecycle.responder_signed_prekey_secret at h
  rcases hp : store.previous_signed_prekey with _ | ⟨sec, pid, sig⟩ <;> simp only [hp] at h <;>
  repeat' first
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals first | exact h | exact h.symm | exact Or.inl h | exact Or.inl h.symm | exact Or.inr h | exact Or.inr h.symm

/-- `responder_kem_slot` refuses only with `LegacyLastResortRecord` or `UnknownPrekeyId`. -/
theorem kem_slot_err (store : lifecycle.PrekeyStore) (id : U32) (e : lifecycle.Error)
    (h : lifecycle.responder_kem_slot store id = ok (core.result.Result.Err e)) :
    e = lifecycle.Error.LegacyLastResortRecord ∨ e = lifecycle.Error.UnknownPrekeyId := by
  unfold lifecycle.responder_kem_slot at h
  rcases hp : store.previous_kem with _ | ⟨kp, pid, sig⟩ <;> simp only [hp] at h <;>
  repeat' first
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals first | exact h | exact h.symm | exact Or.inl h | exact Or.inl h.symm | exact Or.inr h | exact Or.inr h.symm

/-- `responder_curve_inputs` refuses only with `BadEncoding` or `Handshake(InvalidIdentityKey)`. -/
theorem curve_inputs_err (identity ephemeral : Slice U8) (e : lifecycle.Error)
    (h : lifecycle.responder_curve_inputs identity ephemeral = ok (core.result.Result.Err e)) :
    e = lifecycle.Error.BadEncoding ∨
      e = lifecycle.Error.Handshake SessionError.InvalidIdentityKey := by
  unfold lifecycle.responder_curve_inputs at h
  repeat' first
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals first | exact h | exact h.symm | exact Or.inl h | exact Or.inl h.symm | exact Or.inr h | exact Or.inr h.symm

/-- `responder_one_time_key` refuses only with `UnknownPrekeyId`. -/
theorem one_time_key_err (store : lifecycle.PrekeyStore) (id : U32) (e : lifecycle.Error)
    (h : lifecycle.responder_one_time_key store id = ok (core.result.Result.Err e)) :
    e = lifecycle.Error.UnknownPrekeyId := by
  unfold lifecycle.responder_one_time_key at h
  repeat' first
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals first | exact h | exact h.symm | exact Or.inl h | exact Or.inl h.symm | exact Or.inr h | exact Or.inr h.symm

/-- `responder_decapsulate` refuses only with `Kem` or `UnknownPrekeyId`. -/
theorem decapsulate_err (store : lifecycle.PrekeyStore) (slot : lifecycle.KemKeySlot)
    (ct : Slice U8) (e : lifecycle.Error)
    (h : lifecycle.responder_decapsulate store slot ct = ok (core.result.Result.Err e)) :
    e = lifecycle.Error.Kem ∨ e = lifecycle.Error.UnknownPrekeyId := by
  unfold lifecycle.responder_decapsulate at h
  repeat' first
    | (replace h := bind3_eq_ok_inv h; obtain ⟨_, _, _, _, h⟩ := h)
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals first | exact h | exact h.symm | exact Or.inl h | exact Or.inl h.symm | exact Or.inr h | exact Or.inr h.symm

/-- A refused `contributory` check propagates `NonContributoryAgreement` through the `?`. -/
theorem contributory_break_err {T : Type} {o : Option (Array U8 32#usize)}
    {r : core.result.Result (Array U8 32#usize) SessionError}
    {res : core.result.Result core.convert.Infallible SessionError} {e : SessionError}
    (h1 : contributory o = ok r)
    (h2 : core.result.Result.Insts.CoreOpsTry.branch r =
      ok (core.ops.control_flow.ControlFlow.Break res))
    (h3 : core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual T
      (core.convert.FromSame SessionError) res = ok (core.result.Result.Err e)) :
    e = SessionError.NonContributoryAgreement := by
  cases o <;> simp [contributory] at h1 <;> subst h1 <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h2
  subst h2
  simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h3
  exact h3.symm

/-- `responder_shared_secret` refuses only with `InvalidIdentityKey` or `NonContributoryAgreement`. -/
theorem shared_secret_err (ik sp : tacenta_boundary.dh.PrivateKey)
    (otk : Option tacenta_boundary.dh.PrivateKey) (pi pe : tacenta_boundary.dh.PublicKeyBytes)
    (enc : Array U8 32#usize) (e : SessionError)
    (h : responder_shared_secret ik sp otk pi pe enc = ok (core.result.Result.Err e)) :
    e = SessionError.InvalidIdentityKey ∨ e = SessionError.NonContributoryAgreement := by
  unfold responder_shared_secret at h
  repeat' first
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals first
    | exact h | exact h.symm | exact Or.inl h | exact Or.inl h.symm | exact Or.inr h | exact Or.inr h.symm
    | (cases ‹core.convert.Infallible›)
    | skip
  all_goals exact Or.inr (contributory_break_err ‹_› ‹_› h)

/-- `responder_replay_fingerprint` refuses only with `ReplayedLastResort` or `LastResortRecordFull`. -/
theorem replay_err (store : lifecycle.PrekeyStore) (kemId : U32) (sk : Array U8 32#usize)
    (lastResort : Bool) (e : lifecycle.Error)
    (h : lifecycle.responder_replay_fingerprint store kemId sk lastResort =
      ok (core.result.Result.Err e)) :
    e = lifecycle.Error.ReplayedLastResort ∨ e = lifecycle.Error.LastResortRecordFull := by
  unfold lifecycle.responder_replay_fingerprint at h
  repeat' first
    | (replace h := bind_eq_ok_inv h
       obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩, _, h⟩ := h)
    | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
    | split at h
    | simp at h
  all_goals first | exact h | exact h.symm | exact Or.inl h | exact Or.inl h.symm | exact Or.inr h | exact Or.inr h.symm

/-- The first store step of the commit, read off its `if`. -/
theorem commit_kem_step (b : Bool) (store store1 : lifecycle.PrekeyStore) (kemId : U32)
    (h : (if b = true then ok store else do
      let (_, s) ← lifecycle.PrekeyStore.take_one_time_kem store kemId
      ok s) = ok store1) :
    if b then store1 = store
      else ∃ x, lifecycle.PrekeyStore.take_one_time_kem store kemId = ok (x, store1) := by
  cases b
  · simp only [Bool.false_eq_true, if_false] at h ⊢
    obtain ⟨x, s, hx, h⟩ := bind2_eq_ok_inv h
    cases h
    exact ⟨x, hx⟩
  · simp only [if_true] at h ⊢
    simp only [ok.injEq] at h
    exact h.symm

/-- The second store step of the commit, read off its `if`. -/
theorem commit_one_time_step (id : U32) (store1 store2 : lifecycle.PrekeyStore)
    (h : (if (id != serialization.ABSENT_ID) = true then do
      let (_, s) ← lifecycle.PrekeyStore.take_one_time store1 id
      ok s else ok store1) = ok store2) :
    if id != serialization.ABSENT_ID
      then ∃ b, lifecycle.PrekeyStore.take_one_time store1 id = ok (b, store2)
      else store2 = store1 := by
  by_cases hid : (id != serialization.ABSENT_ID) = true
  · simp only [hid, if_true] at h ⊢
    obtain ⟨b, s, hb, h⟩ := bind2_eq_ok_inv h
    cases h
    exact ⟨b, hb⟩
  · simp only [hid, if_false, Bool.false_eq_true] at h ⊢
    simp only [ok.injEq] at h
    exact h.symm

/-! ## The intermediate session's shape -/

open Tacenta.UnitLifecycleEstablishInitiatorShape (singleton_length_le)

/-- The sparse chain table `tacenta_spqr::State::init` builds for the receiving side (`B2a`): one entry at
epoch 0, the sending chain on the second derived key and the receiving chain on the first, both at
counter 0. -/
def responderChains (c1 c2 : Array U8 32#usize) : alloc.vec.Vec (U64 × tacenta_spqr.Chains) :=
  Tacenta.UnitHeadroomSatisfiable.vecOf
    [(0#u64, { send := some { ck := c2, n := 0#u64 }, receive := some { ck := c1, n := 0#u64 } })]
    (singleton_length_le _)

/-- The Triple state `tacenta_triple::State::init_receiver` builds, with the derived keys as arguments: our
ratchet key, no peer key and no chains on the classical side; one chain-table entry at epoch 0 in the
receiving direction on the sparse side. -/
def responderTriple (a rk prk c1 c2 : Array U8 32#usize) : tacenta_triple.State :=
  { classical :=
      { dhs_pub := a, dhr_pub := none, rk := rk, cks := none, ckr := none,
        ns := 0#u32, nr := 0#u32, pn := 0#u32, skipped := alloc.vec.Vec.new tacenta_ratchet.SkippedKey,
        events := 0#u32, labels := tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := prk, epoch := 0#u64, chains := responderChains c1 c2,
        skipped := alloc.vec.Vec.new tacenta_spqr.Skipped, direction := tacenta_spqr.Direction.B2a } }

/-- A successful `init_receiver` returns `responderTriple` of its public key and some derived keys. -/
theorem init_receiver_ok (sk : Slice U8) (a : Array U8 32#usize) (t : tacenta_triple.State)
    (h : tacenta_triple.State.init_receiver sk a tacenta_ratchet.LabelSet.Tacenta = ok t) :
    ∃ rk prk c1 c2, t = responderTriple a rk prk c1 c2 := by
  unfold tacenta_triple.State.init_receiver tacenta_ratchet.init_receiver tacenta_spqr.State.init_bob
    tacenta_spqr.State.init at h
  obtain ⟨ec, pq, -, h⟩ := bind2_eq_ok_inv h
  obtain ⟨cl, hcl, h⟩ := bind_eq_ok_inv h
  obtain ⟨s1, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨pqs, hpq, h⟩ := bind_eq_ok_inv h
  obtain ⟨prk, k1, k2, -, hpq⟩ := bind3_eq_ok_inv hpq
  obtain ⟨-, -, h⟩ := bind_eq_ok_inv h
  obtain ⟨-, -, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq] at h
  simp at hcl
  simp [lift] at hpq
  subst h hcl hpq
  exact ⟨ec, prk, k1, k2, rfl⟩

/-- A successful `Braid::responder` returns a `NoHeaderReceived` Braid at epoch 1 holding the decoder
`hdr_decoder` returned. -/
theorem braid_responder_ok (s : Slice U8) (b : tacenta_braid.Braid)
    (h : tacenta_braid.Braid.responder s = ok b) :
    ∃ auth d, tacenta_braid.hdr_decoder = ok d ∧
      b = ⟨tacenta_braid.State.NoHeaderReceived 1#u64 auth d⟩ := by
  unfold tacenta_braid.Braid.responder at h
  obtain ⟨auth, _, h⟩ := bind_eq_ok_inv h
  obtain ⟨d, hd, h⟩ := bind_eq_ok_inv h
  simp at h
  exact ⟨auth, d, hd, h.symm⟩

/-- A successful `hdr_decoder` returns a fresh decoder sized for the header and its MAC. -/
theorem hdr_decoder_ok (d : tacenta_erasure.Decoder) (h : tacenta_braid.hdr_decoder = ok d) :
    ∃ hv n needed, tacenta_kem.HEADER_LEN = ok hv ∧ hv + tacenta_braid.MAC_LEN = ok n ∧
      n.val = hv.val + 32 ∧
      tacenta_erasure.chunk_count n = ok needed ∧
      d = { size := n, needed := needed, «have» := alloc.vec.Vec.new tacenta_erasure.Chunk } := by
  unfold tacenta_braid.hdr_decoder tacenta_erasure.Decoder.new at h
  obtain ⟨hv, hhv, h⟩ := bind_eq_ok_inv h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_inv h
  obtain ⟨needed, hneeded, h⟩ := bind_eq_ok_inv h
  simp only [ok.injEq] at h
  have hn' : n.val = hv.val + 32 := by
    have : tacenta_braid.MAC_LEN.val = 32 := by simp [tacenta_braid.MAC_LEN]
    have := UScalar.add_equiv hv tacenta_braid.MAC_LEN
    rw [hn] at this
    simp at this
    omega
  exact ⟨hv, n, needed, hhv, hn, hn', hneeded, h.symm⟩

/-- A `Vec<u8>` clone is the vector itself. -/
theorem vecU8_clone_eq {v v' : alloc.vec.Vec U8}
    (h : alloc.vec.CloneVec.clone core.clone.CloneU8 v = ok v') : v' = v := by
  obtain ⟨r, hr, hp⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.vecU8_clone_no_panic v)
  rw [hr] at h
  cases h
  exact hp.symm

/-- What a successful `responder_curve_inputs` checked: both keys decode, and the identity key passes
`is_valid_identity_key`. -/
theorem curve_inputs_ok (identity ephemeral : Slice U8) (a b : tacenta_boundary.dh.PublicKeyBytes)
    (h : lifecycle.responder_curve_inputs identity ephemeral = ok (core.result.Result.Ok (a, b))) :
    decode_ec identity = ok (some a) ∧ is_valid_identity_key a = ok true ∧
      decode_ec ephemeral = ok (some b) := by
  unfold lifecycle.responder_curve_inputs at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_inv h
  rcases o with _ | a'
  · simp at h
  simp only at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_inv h
  cases v
  · simp at h
  simp only [if_true] at h
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_inv h
  rcases o1 with _ | b'
  · simp at h
  simp only [ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨ho, hv, ho1⟩

/-- The two private keys `establish_responder` computes from the signed prekey's bytes are one key. -/
theorem ResponderPreparedParts.ratchetPrivate_eq (p : ResponderPreparedParts our store msg) :
    p.ratchetPrivate = p.signedPrekey := by
  have h := p.hRatchetPrivate.symm.trans p.hSignedPrekey
  simpa using h

/-- The two slices of the shared secret `establish_responder` takes are one slice. -/
theorem ResponderPreparedParts.braidSecret_eq (p : ResponderPreparedParts our store msg) :
    p.braidSecret = p.tripleSecret := by
  have h := p.hBraidSecret.symm.trans p.hTripleSecret
  simpa using h

/-- The established-ephemeral copy is the initial message's ephemeral key. -/
theorem ResponderPreparedParts.ephemeralCopy_eq (p : ResponderPreparedParts our store msg) :
    p.ephemeralCopy = p.decoded.ephemeral :=
  vecU8_clone_eq p.hEphemeralCopy

/-! ## `Session::invariant` of the intermediate session -/

open Tacenta.UnitHeadroomInvariant (OptionEqU64Shape is_canonical_key_eq is_valid_identity_key_eq
  vec_ne_self array_ne_self)
open Tacenta.UnitLifecycleEstablishInitiatorShape (DhPublicValid dhPublicValid_canonical
  dhPublicValid_valid identity_public_valid)

/-- A fresh decoder whose `needed` is the chunk count of its size, and at most `MAX_CODEWORDS`, passes the
translated `Decoder::invariant`: its loop runs over no chunk. -/
theorem fresh_decoder_invariant (n needed : Usize) (hcc : tacenta_erasure.chunk_count n = ok needed)
    (hle : needed.val ≤ 65536) :
    tacenta_erasure.Decoder.invariant
      { size := n, needed := needed, «have» := alloc.vec.Vec.new tacenta_erasure.Chunk } = ok true := by
  unfold tacenta_erasure.Decoder.invariant tacenta_erasure.Decoder.invariant_loop
  dsimp only
  rw [loop.eq_def]
  simp [tacenta_erasure.Decoder.invariant_loop.body, alloc.vec.Vec.new, alloc.vec.Vec.len, hcc,
    tacenta_erasure.MAX_CODEWORDS]
  scalar_tac

/-- The decoder a successful `hdr_decoder` returns passes `Braid`'s check of a `NoHeaderReceived` decoder,
under the value law of `div_ceil` and the bound of `HEADER_LEN` the Braid receive contracts carry. -/
theorem hdr_decoder_checks (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hhdr : Tacenta.SessionUnitBraidT1.HeaderLenTotal) (d : tacenta_erasure.Decoder)
    (h : tacenta_braid.hdr_decoder = ok d) :
    tacenta_erasure.Decoder.invariant d = ok true ∧
      (do
        let i ← tacenta_kem.HEADER_LEN
        let i1 ← i + tacenta_braid.MAC_LEN
        tacenta_braid.decoder_sized d i1) = ok true := by
  obtain ⟨hv, n, needed, hhv, hadd, hn, hcc, rfl⟩ := hdr_decoder_ok d h
  obtain ⟨hv', hhv', hle⟩ := hhdr
  rw [hhv] at hhv'
  cases hhv'
  obtain ⟨r, hr, hrv⟩ := hdiv n
  have hr' : tacenta_erasure.chunk_count n = ok r := by
    unfold tacenta_erasure.chunk_count; simpa [tacenta_erasure.CHUNK_BYTES] using hr
  rw [hcc] at hr'
  cases hr'
  refine ⟨fresh_decoder_invariant n needed hcc (by omega), ?_⟩
  simp [hhv, hadd, tacenta_braid.decoder_sized, tacenta_erasure.Decoder.impl.size]

/-- `Triple::invariant` of the Triple `init_receiver` builds, given its public key is canonical. -/
theorem responderTriple_invariant (a rk prk c1 c2 : Array U8 32#usize)
    (ha : Tacenta.SessionUnitT1.canonicalX25519 a = true) :
    tacenta_triple.State.invariant (responderTriple a rk prk c1 c2) = ok true := by
  have h1 : tacenta_ratchet.State.invariant (responderTriple a rk prk c1 c2).classical = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Ratchet.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [responderTriple, alloc.vec.Vec.new, tacenta_ratchet.MAX_SKIPPED_STORE]
    · simp [responderTriple, U32.max_eq]
    · simp [responderTriple, alloc.vec.Vec.new]
    · simp [responderTriple, alloc.vec.Vec.new]
    · simp [responderTriple]
    · simpa [responderTriple] using ha
    · simp [responderTriple]
    · simp [responderTriple, alloc.vec.Vec.new]
  have h2 : tacenta_spqr.State.invariant (responderTriple a rk prk c1 c2).post_quantum = ok true := by
    rw [Tacenta.SessionUnitRatchetImportInv.Spqr.invariant_true_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [responderTriple, alloc.vec.Vec.new, tacenta_spqr.MAX_SKIPPED_STORE]
    · simp [responderTriple, responderChains, Tacenta.UnitHeadroomSatisfiable.vecOf,
        core.num.U64.saturating_add, UScalar.saturating_add, tacenta_spqr.EPOCHS_KEPT, U64.max_eq]
      decide
    · simp [responderTriple, responderChains, Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [responderTriple, responderChains, Tacenta.UnitHeadroomSatisfiable.vecOf]
    · simp [responderTriple, alloc.vec.Vec.new]
    · simp [responderTriple, alloc.vec.Vec.new]
  simp only [responderTriple] at h1 h2
  unfold tacenta_triple.State.invariant
  simp [h1, h2, responderTriple, tacenta_spqr.State.impl.direction,
    tacenta_ratchet.State.started_as_sender]

/-- `Session::structural_invariant` of the session `establish_responder` hands to `decrypt_ratchet`. -/
theorem responder_structural (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (p : ResponderPreparedParts our store msg) :
    lifecycle.Session.structural_invariant p.session = ok true := by
  obtain ⟨rk, prk, c1, c2, htriple⟩ := init_receiver_ok _ _ _ p.hTriple
  obtain ⟨auth, d, -, hbraid⟩ := braid_responder_ok _ _ p.hBraid
  obtain ⟨-, hvalid, hdecEph⟩ := curve_inputs_ok _ _ _ _ p.hCurve
  have hv := identity_public_valid hpub p.hOurPublic
  have hpriv := p.ratchetPrivate_eq
  have heph := p.ephemeralCopy_eq
  unfold lifecycle.Session.structural_invariant
  simp [ResponderPreparedParts.session, htriple, hbraid, hpriv, heph, p.hRatchetPublic, p.hRatchetBytes,
    responderTriple, tacenta_triple.State.sending_public, tacenta_ratchet.State.sending_public,
    array_ne_self, tacenta_braid.Braid.failed, tacenta_braid.Braid.is_initiator, tacenta_braid.State.epoch,
    lifecycle.Session.is_responder, p.hIdentityAd, vec_ne_self, tacenta_triple.State.direction,
    tacenta_spqr.State.impl.direction, hv, hvalid, hdecEph,
    tacenta_braid.Braid.epoch, tacenta_triple.State.epoch, tacenta_spqr.State.impl.epoch,
    tacenta_braid.Braid.state_tag, lift, tacenta_spqr.Direction.Insts.CoreCmpPartialEqDirection.eq]
  have h01 : U64.checked_add 0#u64 1#u64 = some 1#u64 := by decide
  rw [h01, hoeq]
  have hmod : (1#u64 % 2#u64 : Result U64) = ok 1#u64 := by
    obtain ⟨z, hz, hzv⟩ := Std.WP.spec_imp_exists (UScalar.rem_spec 1#u64 (y := 2#u64) (by decide))
    have hz1 : z = 1#u64 := by apply UScalar.eq_of_val_eq; simp at hzv ⊢; omega
    rw [hz, hz1]
  simp [hmod, tacenta_spqr.Direction.read_discriminant]

/-- **`Session::invariant` of the session `establish_responder` hands to `decrypt_ratchet`**, for every
input that reaches the inner call, under the assumed law `DhPublicValid`, the recorded assumption
`OptionEqU64Shape`, the value law of `div_ceil` (`DivCeilValue`) and the bound on `HEADER_LEN` the Braid
receive contracts carry (`HeaderLenTotal`). -/
theorem responder_prepared_invariant (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (hhdr : Tacenta.SessionUnitBraidT1.HeaderLenTotal)
    (p : ResponderPreparedParts our store msg) :
    lifecycle.Session.invariant p.session = ok true := by
  unfold lifecycle.Session.invariant
  rw [responder_structural hpub hoeq p]
  simp only [Aeneas.Std.bind_tc_ok, if_true]
  unfold lifecycle.Session.leaf_invariants
  obtain ⟨rk, prk, c1, c2, htriple⟩ := init_receiver_ok _ _ _ p.hTriple
  obtain ⟨auth, d, hd, hbraid⟩ := braid_responder_ok _ _ p.hBraid
  have ha := dhPublicValid_canonical hpub p.hRatchetPublic p.hRatchetBytes
  obtain ⟨hdinv, hsized⟩ := hdr_decoder_checks hdiv hhdr d hd
  simp only [ResponderPreparedParts.session, htriple, hbraid]
  rw [responderTriple_invariant _ _ _ _ _ ha]
  simp only [Aeneas.Std.bind_tc_ok, if_true, tacenta_braid.Braid.invariant]
  simp [hdinv]
  exact hsized

/-! ## The four counter ceilings of the intermediate session -/

/-- **All four counter ceilings hold at the intermediate session**, with no hypothesis: the classical clock
and both sparse chain counters are 0, the sparse epoch is 0, the Braid epoch is 1. -/
theorem counterHeadroom_responder_prepared (p : ResponderPreparedParts our store msg) :
    Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom p.session := by
  obtain ⟨rk, prk, c1, c2, htriple⟩ := init_receiver_ok _ _ _ p.hTriple
  obtain ⟨auth, d, -, hbraid⟩ := braid_responder_ok _ _ p.hBraid
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ResponderPreparedParts.session, htriple, responderTriple, U32.max_eq]
  · simp [ResponderPreparedParts.session, htriple, responderTriple, U64.max_eq]
  · intro q hq ch hch
    simp [ResponderPreparedParts.session, htriple, responderTriple, responderChains,
      Tacenta.UnitHeadroomSatisfiable.vecOf] at hq
    subst hq
    rcases hch with h | h <;> (simp at h; subst h; simp [U64.max_eq])
  · simp only [ResponderPreparedParts.session, hbraid, Tacenta.SessionUnitBraidT1.State.epoch_val]
    scalar_tac

/-! ## The model session, and the relation -/

open Tacenta.UnitLifecycleT3 (DhView SessionRefines vecOf sliceOf)

/-- **The model session the intermediate session stands for**: the Triple through `ratchetAbs`/`spqrAbs`,
the identities, associated data, ratchet key and established ephemeral through the DH view, and the Braid
as the model's initial responder state `Model.Braid.initBob` of the secret `Braid::responder` was given.
It is read off the code's session; it is not shown to be the session `Model.Lifecycle.prepareResponder`
builds. -/
def responderModelOf (dh : DhView) (p : ResponderPreparedParts our store msg) :
    Model.Lifecycle.Session :=
  { triple :=
      { classical := Tacenta.SessionUnitTripleT3.ratchetAbs p.triple.classical
        postQuantum := Tacenta.SessionUnitTripleT3.spqrAbs p.triple.post_quantum }
    braid := Model.Braid.initBob (sliceOf p.braidSecret)
    ratchetPrivate := dh.privateKey p.ratchetPrivate
    identityAd := vecOf p.identityAd
    ourIdentityPublic := dh.publicKey p.ourPublic
    peerIdentityPublic := dh.publicKey p.peerIdentity
    pendingInitial := none
    establishedEphemeral := some (vecOf p.ephemeralCopy) }

/-- **The intermediate session refines `responderModelOf`**, for every DH view and KEM, under the Braid
agreements `Braid::responder`'s refinement takes (`UnitSatisfiabilityBraidStates.responder_refines`).  Every
field but the Braid is an equation through the abstraction functions; the Braid half is that theorem. -/
theorem sessionRefines_responder_prepared (hea : Tacenta.SessionUnitBraidT3.ErasureAgrees)
    {K : Model.Braid.Kem} (hlens : Tacenta.SessionUnitBraidT3.KemLenAgrees K)
    (hkdf : Tacenta.SessionUnitBraidT3.BraidHkdfAgrees)
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue) (dh : DhView)
    (p : ResponderPreparedParts our store msg) :
    SessionRefines dh K p.session (responderModelOf dh p) := by
  obtain ⟨b, hb, hpost⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitSatisfiabilityBraidStates.responder_refines (K := K) hea hlens hkdf hz hdiv p.braidSecret)
  rw [p.hBraid] at hb
  cases hb
  exact ⟨⟨rfl, rfl⟩, hpost.1, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `HonestChunk` at the model session asks exactly that a header chunk of epoch 1 comes from a message of
the header's size (96 bytes: the decoder holds nothing yet); it asks nothing of any other message. -/
theorem honestChunk_responder_iff (dh : DhView) (p : ResponderPreparedParts our store msg)
    (msg' : Model.Braid.Msg) :
    Tacenta.SessionUnitBraidT3.HonestChunk (responderModelOf dh p).braid msg' ↔
      ∀ mc, msg'.data = some mc → msg'.epoch = 1 → msg'.type = .hdr →
        mc.source.length = Model.Braid.headerSize + Model.Braid.macSize := by
  unfold Tacenta.SessionUnitBraidT3.HonestChunk
  simp only [responderModelOf, Model.Braid.initBob, Model.Braid.BraidState.epoch]
  constructor
  · intro h mc hd he ht
    have := h mc hd he
    rw [ht] at this
    exact this.1
  · intro h mc hd he
    cases ht : msg'.type <;> simp only [ht] <;> try trivial
    exact ⟨h mc hd he ht, by simp [Model.Braid.Decoder.new]⟩

/-! ## The model step's draws -/

/-- The model's `decryptRatchet` either keeps the oracle or takes exactly one draw from it, and a success
takes exactly one. -/
theorem decryptRatchet_oracle (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (session : Model.Lifecycle.Session) (message : Model.Lifecycle.Bytes) :
    ((Model.Lifecycle.decryptRatchet view oracle session message).oracle = oracle ∨
      ∃ c, Model.Lifecycle.random32 oracle =
        some (c, (Model.Lifecycle.decryptRatchet view oracle session message).oracle)) ∧
    (∀ pt, (Model.Lifecycle.decryptRatchet view oracle session message).result = .ok pt →
      ∃ c, Model.Lifecycle.random32 oracle =
        some (c, (Model.Lifecycle.decryptRatchet view oracle session message).oracle)) := by
  unfold Model.Lifecycle.decryptRatchet
  split
  · simp
  split
  · simp
  dsimp only
  split
  · simp
  split
  · simp
  rename_i c o hr
  split
  · simp [hr]
  split
  · simp [hr]
  split
  · simp [hr]
  · simp [hr]

/-! ## What the commit does to the store -/

/-- The loop of `take_one_time_kem` returns the store's own fields and an index, if any. -/
theorem take_one_time_kem_loop_frame (store : lifecycle.PrekeyStore) (id : U32) (index : Usize)
    (hindex : index.val ≤ store.kem_one_time.val.length) :
    lifecycle.PrekeyStore.take_one_time_kem_loop store id index ⦃ fun r =>
      ∃ found, r = (store.identity_public, store.signed_prekey_secret, store.signed_prekey_id,
        store.signed_prekey_sig, store.one_time, store.kem, store.kem_id, store.kem_sig,
        store.kem_one_time, store.previous_signed_prekey, store.previous_kem, store.next_id,
        store.last_resort_seen, store.legacy_last_resort_blocked, found) ⦄ := by
  unfold lifecycle.PrekeyStore.take_one_time_kem_loop
  apply loop.spec_decr_nat
    (measure := fun i => store.kem_one_time.val.length - i.val)
    (inv := fun i => i.val ≤ store.kem_one_time.val.length)
  · intro index1 hi
    simp only [lifecycle.PrekeyStore.take_one_time_kem_loop.body]
    simp only [alloc.vec.Vec.len]
    split
    · step
      split
      · simp
      · step
        case hmax => scalar_tac
        case a => constructor <;> scalar_tac
    · simp
  · exact hindex

/-- **`take_one_time_kem` changes only the one-time KEM prekeys.** -/
theorem take_one_time_kem_frame (store : lifecycle.PrekeyStore) (id : U32)
    (x : Option tacenta_boundary.kem.KeyPair) (store' : lifecycle.PrekeyStore)
    (h : lifecycle.PrekeyStore.take_one_time_kem store id = ok (x, store')) :
    store' = { store with kem_one_time := store'.kem_one_time } := by
  unfold lifecycle.PrekeyStore.take_one_time_kem at h
  obtain ⟨⟨pkb, a, i, a1, z, kp, i1, a2, v, o, o1, i2, v1, v2, found⟩, hr, h⟩ := bind_eq_ok_inv h
  obtain ⟨r', hr', ⟨found', rfl⟩⟩ := Std.WP.spec_imp_exists
    (take_one_time_kem_loop_frame store id 0#usize (by simp))
  rw [hr] at hr'
  simp only [ok.injEq, Prod.mk.injEq] at hr'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hr'
  rcases found with _ | i3
  · simp at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · simp at h
    repeat' first
      | (replace h := bind2_eq_ok_inv h; obtain ⟨_, _, _, h⟩ := h)
      | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
      | split at h
      | simp at h
    all_goals first
      | (obtain ⟨-, rfl⟩ := h; rfl)
      | (subst h; rfl)
      | (rw [← h.2])

/-- The loop of `take_one_time` returns the store's own fields and an index, if any. -/
theorem take_one_time_loop_frame [Tacenta.SessionUnitT1.DerivedKeysModel]
    (store : lifecycle.PrekeyStore) (id : U32) (index : Usize)
    (hindex : index.val ≤
      (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length) :
    lifecycle.PrekeyStore.take_one_time_loop store id index ⦃ fun r =>
      ∃ found, r = (store.identity_public, store.signed_prekey_secret, store.signed_prekey_id,
        store.signed_prekey_sig, store.one_time, store.kem, store.kem_id, store.kem_sig,
        store.kem_one_time, store.previous_signed_prekey, store.previous_kem, store.next_id,
        store.last_resort_seen, store.legacy_last_resort_blocked, found) ⦄ := by
  unfold lifecycle.PrekeyStore.take_one_time_loop
  apply loop.spec_decr_nat
    (measure := fun i =>
      (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length - i.val)
    (inv := fun i => i.val ≤
      (Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time).val.length)
  · intro index1 hi
    simp only [lifecycle.PrekeyStore.take_one_time_loop.body]
    step
    split
    · step
      split
      · simp
      · step
        case hmax => scalar_tac
        case a => constructor <;> scalar_tac
    · simp
  · exact hindex

/-- **`take_one_time` changes only the one-time curve prekeys**, given the model of the zeroizing wrapper
its loop reads through (`DerivedKeysModel`, which the decrypt theorems also take). -/
theorem take_one_time_frame [Tacenta.SessionUnitT1.DerivedKeysModel]
    (store : lifecycle.PrekeyStore) (id : U32) (b : Bool) (store' : lifecycle.PrekeyStore)
    (h : lifecycle.PrekeyStore.take_one_time store id = ok (b, store')) :
    store' = { store with one_time := store'.one_time } := by
  unfold lifecycle.PrekeyStore.take_one_time at h
  obtain ⟨⟨pkb, a, i, a1, z, kp, i1, a2, v, o, o1, i2, v1, v2, found⟩, hr, h⟩ := bind_eq_ok_inv h
  obtain ⟨r', hr', ⟨found', rfl⟩⟩ := Std.WP.spec_imp_exists
    (take_one_time_loop_frame store id 0#usize (by simp))
  rw [hr] at hr'
  simp only [ok.injEq, Prod.mk.injEq] at hr'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hr'
  rcases found with _ | i3
  · simp at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · simp at h
    repeat' first
      | (replace h := bind2_eq_ok_inv h; obtain ⟨_, _, _, h⟩ := h)
      | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
      | split at h
      | simp at h
    all_goals first
      | (obtain ⟨-, rfl⟩ := h; rfl)
      | (subst h; rfl)
      | (rw [← h.2])

/-- `Vec::push` that returns appends the element. -/
theorem vec_push_ok {α : Type} {v v' : alloc.vec.Vec α} {x : α} (h : alloc.vec.Vec.push v x = ok v') :
    v'.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · cases h; simp
  · cases h

/-- **What the success commit does to the store**: every field but the one-time curve prekeys, the one-time
KEM prekeys and the replay record is the store's own; the one-time KEM prekeys are untouched on the
last-resort path; the one-time curve prekeys are untouched when the message names none; the replay record is
untouched unless a fingerprint was computed, and otherwise gains exactly `(kemId, fp)` at its end.  Which
entry the two removals take is not stated here. -/
theorem responderCommit_effects [Tacenta.SessionUnitT1.DerivedKeysModel]
    {store store' : lifecycle.PrekeyStore} {kemId oneTimeId : U32} {lastResort : Bool}
    {replay : Option (Array U8 32#usize)}
    (h : ResponderCommit store kemId oneTimeId lastResort replay store') :
    store' = { store with one_time := store'.one_time, kem_one_time := store'.kem_one_time, last_resort_seen := store'.last_resort_seen } ∧
    (lastResort = true → store'.kem_one_time = store.kem_one_time) ∧
    (oneTimeId = serialization.ABSENT_ID → store'.one_time = store.one_time) ∧
    (replay = none → store'.last_resort_seen = store.last_resort_seen) ∧
    (∀ fp, replay = some fp →
      store'.last_resort_seen.val = store.last_resort_seen.val.concat (kemId, fp)) := by
  obtain ⟨store1, store2, c1, c2, c3⟩ := h
  have h1 : store1 = { store with kem_one_time := store1.kem_one_time } ∧
      (lastResort = true → store1.kem_one_time = store.kem_one_time) := by
    cases lastResort
    · simp only [Bool.false_eq_true, if_false] at c1
      obtain ⟨x, hx⟩ := c1
      exact ⟨take_one_time_kem_frame _ _ _ _ hx, by simp⟩
    · simp only [if_true] at c1
      subst c1
      exact ⟨rfl, fun _ => rfl⟩
  have h2 : store2 = { store1 with one_time := store2.one_time } ∧
      (oneTimeId = serialization.ABSENT_ID → store2.one_time = store1.one_time) := by
    by_cases hid : (oneTimeId != serialization.ABSENT_ID) = true
    · simp only [hid, if_true] at c2
      obtain ⟨b, hb⟩ := c2
      refine ⟨take_one_time_frame _ _ _ _ hb, fun habs => ?_⟩
      simp [habs] at hid
    · simp only [hid, if_false, Bool.false_eq_true] at c2
      subst c2
      exact ⟨rfl, fun _ => rfl⟩
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have h12 : store2 = { store with one_time := store2.one_time, kem_one_time := store2.kem_one_time } := by
    rw [h2a, h1a]
  rcases replay with _ | fp
  · simp only at c3
    subst c3
    refine ⟨by rw [h12], fun hl => ?_, fun ho => ?_, fun _ => ?_, fun fp hfp => (by cases hfp)⟩
    · rw [h2a]; exact h1b hl
    · rw [h2b ho, h1a]
    · rw [h2a, h1a]
  · simp only at c3
    obtain ⟨count, seen, -, -, hseen, rfl⟩ := c3
    have hs := vec_push_ok hseen
    refine ⟨?_, fun hl => ?_, fun ho => ?_, fun h => (by cases h), fun fp' hfp => ?_⟩
    · conv_lhs => rw [h12]
    · show store2.kem_one_time = _
      rw [h2a]; exact h1b hl
    · show store2.one_time = _
      rw [h2b ho, h1a]
    · cases hfp
      rw [hs, h2a, h1a]
      simp

/-- What a successful `responder_replay_fingerprint` returns: nothing on the one-time path, and on the
last-resort path the HMAC fingerprint `last_resort_fingerprint` of the shared secret. -/
theorem replay_ok (store : lifecycle.PrekeyStore) (kemId : U32) (sk : Array U8 32#usize)
    (lastResort : Bool) (r : Option (Array U8 32#usize))
    (h : lifecycle.responder_replay_fingerprint store kemId sk lastResort =
      ok (core.result.Result.Ok r)) :
    (lastResort = false → r = none) ∧
      (lastResort = true → ∃ fp, r = some fp ∧ lifecycle.last_resort_fingerprint sk = ok fp) := by
  unfold lifecycle.responder_replay_fingerprint at h
  cases lastResort
  · simp at h
    exact ⟨fun _ => h.symm, fun h => (by cases h)⟩
  · simp only [if_true] at h
    obtain ⟨fp, hfp, h⟩ := bind_eq_ok_inv h
    refine ⟨fun h => (by cases h), fun _ => ⟨fp, ?_, hfp⟩⟩
    repeat' first
      | (replace h := bind_eq_ok_inv h
         obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩, _, h⟩ := h)
      | (replace h := bind_eq_ok_inv h; obtain ⟨_, _, h⟩ := h)
      | split at h
      | simp at h
    all_goals first | exact h | exact h.symm

/-- **Every return of `establish_responder`, for every identity, prekey store, initial message and source of
randomness, is one of three outcomes, each with its effects.**  Hypothesis-free.
* A refusal before the inner receive: one of the errors of `PrepareRefusal`, the store and the random source
  returned as given, no session.
* The inner `decrypt_ratchet` on `p.session` and `p.message` (parts read off the code) refused: its error,
  the store as given, the random source `decrypt_ratchet` returned.
* The inner receive succeeded: its plaintext and session, the store after `ResponderCommit`, the random
  source `decrypt_ratchet` returned. -/
theorem establish_responder_cases {R : Type} (rc : rand_core_1.RngCore R) (crc : rand_core_1.CryptoRng R)
    (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (msg : Slice U8) (rng : R)
    (out : core.result.Result (lifecycle.Session × alloc.vec.Vec U8) lifecycle.Error ×
      lifecycle.PrekeyStore × R)
    (h : lifecycle.establish_responder rc crc our store msg rng = ok out) :
    (∃ e, PrepareRefusal e ∧ out = (core.result.Result.Err e, store, rng)) ∨
    ∃ (p : ResponderPreparedParts our store msg)
      (inner : core.result.Result (alloc.vec.Vec U8) lifecycle.Error × lifecycle.Session × R),
      lifecycle.Session.decrypt_ratchet rc crc p.session p.message rng = ok inner ∧
      ((∃ e, inner.1 = core.result.Result.Err e ∧ out = (core.result.Result.Err e, store, inner.2.2)) ∨
       (∃ pt store', inner.1 = core.result.Result.Ok pt ∧
          ResponderCommit store p.decoded.kem_prekey_id p.decoded.one_time_prekey_id p.lastResort
            p.replay store' ∧
          out = (core.result.Result.Ok (inner.2.1, pt), store', inner.2.2))) := by
  unfold lifecycle.establish_responder at h
  replace h := bind_eq_ok_inv h
  obtain ⟨r0, hr0, h⟩ := h
  rcases r0 with decoded | e0
  swap
  · simp at h; exact Or.inl ⟨_, Or.inl ⟨_, rfl⟩, h.symm⟩
  simp only at h
  replace h := bind_eq_ok_inv h
  obtain ⟨r1, hr1, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨cf1, hcf1, h⟩ := h
  rcases r1 with signedSecret | e1 <;>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf1 <;> subst hcf1
  swap
  · simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    exact Or.inl ⟨_, by have := signed_prekey_err _ _ _ hr1; simp [PrepareRefusal, this], h.symm⟩
  simp only at h
  replace h := bind_eq_ok_inv h
  obtain ⟨r2, hr2, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨cf2, hcf2, h⟩ := h
  rcases r2 with ⟨kemSlot, lastResort⟩ | e2 <;>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf2 <;> subst hcf2
  swap
  · simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    exact Or.inl ⟨_, by rcases kem_slot_err _ _ _ hr2 with h' | h' <;> simp [PrepareRefusal, h'], h.symm⟩
  simp only at h
  replace h := bind_eq_ok_inv h
  obtain ⟨lr1, hlr1, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨r3, hr3, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨cf3, hcf3, h⟩ := h
  rcases r3 with ⟨peerIdentity, peerEphemeral⟩ | e3 <;>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf3 <;> subst hcf3
  swap
  · simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    exact Or.inl ⟨_, by rcases curve_inputs_err _ _ _ hr3 with h' | h' <;> simp [PrepareRefusal, h'], h.symm⟩
  simp only at h
  replace h := bind_eq_ok_inv h
  obtain ⟨r4, hr4, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨cf4, hcf4, h⟩ := h
  rcases r4 with oneTime | e4 <;>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf4 <;> subst hcf4
  swap
  · simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    exact Or.inl ⟨_, by have := one_time_key_err _ _ _ hr4; simp [PrepareRefusal, this], h.symm⟩
  simp only at h
  replace h := bind_eq_ok_inv h
  obtain ⟨r5, hr5, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨cf5, hcf5, h⟩ := h
  rcases r5 with kemSecret | e5 <;>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf5 <;> subst hcf5
  swap
  · simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    exact Or.inl ⟨_, by rcases decapsulate_err _ _ _ _ hr5 with h' | h' <;> simp [PrepareRefusal, h'], h.symm⟩
  simp only at h
  replace h := bind_eq_ok_inv h
  obtain ⟨kemSecretZ, hKemSecretZ, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨signedBytes, hSignedBytes, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨signedPrekey, hSignedPrekey, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨sharedR, hSharedR, h⟩ := h
  have hSharedR' : ∃ (identityKey : tacenta_boundary.dh.PrivateKey) (encapsulated : Array U8 32#usize),
      lifecycle.Identity.dh_key our = ok identityKey ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref z32 kemSecretZ = ok encapsulated ∧
      responder_shared_secret identityKey signedPrekey oneTime peerIdentity peerEphemeral encapsulated =
        ok sharedR := by
    cases oneTime <;> simp only at hSharedR <;>
    · obtain ⟨k, hk, hSharedR⟩ := bind_eq_ok_inv hSharedR
      obtain ⟨a, ha, hSharedR⟩ := bind_eq_ok_inv hSharedR
      exact ⟨k, a, hk, ha, hSharedR⟩
  clear hSharedR
  rcases sharedR with shared | eShared
  swap
  · simp at h
    obtain ⟨_, _, -, -, hss⟩ := hSharedR'
    exact Or.inl ⟨_, by rcases shared_secret_err _ _ _ _ _ _ _ hss with h' | h' <;> simp [PrepareRefusal, h'], h.symm⟩
  simp only at h
  replace h := bind_eq_ok_inv h
  obtain ⟨secretZ, hSecretZ, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨secret, hSecret, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨r6, hr6, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨cf6, hcf6, h⟩ := h
  rcases r6 with replay | e6 <;>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf6 <;> subst hcf6
  swap
  · simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    exact Or.inl ⟨_, by rcases replay_err _ _ _ _ _ hr6 with h' | h' <;> simp [PrepareRefusal, h'], h.symm⟩
  simp only at h
  replace h := bind_eq_ok_inv h
  obtain ⟨tripleSecret, hTripleSecret, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨ratchetPublic, hRatchetPublic, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨ratchetBytes, hRatchetBytes, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨triple, hTriple, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨braidSecret, hBraidSecret, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨braid, hBraid, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨ratchetPrivate, hRatchetPrivate, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨ourPublic, hOurPublic, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨identityAd, hIdentityAd, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨ephemeralCopy, hEphemeralCopy, h⟩ := h
  have hlr : lr1 = lastResort := by
    cases lastResort <;> simp at hlr1 <;> exact hlr1
  subst hlr
  have hShared := hSharedR'
  let p : ResponderPreparedParts our store msg :=
    { decoded, signedSecret, kemSlot, lastResort := lr1, peerIdentity, peerEphemeral, oneTime,
      kemSecret, kemSecretZ, signedBytes, signedPrekey, shared, secretZ, secret, replay,
      tripleSecret, ratchetPublic, ratchetBytes, triple, braidSecret, braid, ratchetPrivate,
      ourPublic, identityAd, ephemeralCopy, hDecode := hr0, hSigned := hr1, hSlot := hr2,
      hCurve := hr3, hOneTime := hr4, hDecaps := hr5, hKemSecretZ, hSignedBytes, hSignedPrekey,
      hShared, hSecretZ, hSecret, hReplay := hr6, hTripleSecret, hRatchetPublic, hRatchetBytes,
      hTriple, hBraidSecret, hBraid, hRatchetPrivate, hOurPublic, hIdentityAd, hEphemeralCopy }
  replace h := bind3_eq_ok_inv h
  obtain ⟨r7, session', rng1, hinner, h⟩ := h
  refine Or.inr ⟨p, (r7, session', rng1), hinner, ?_⟩
  replace h := bind_eq_ok_inv h
  obtain ⟨cf7, hcf7, h⟩ := h
  rcases r7 with pt | e7 <;>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, ok.injEq] at hcf7 <;> subst hcf7
  swap
  · simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    exact Or.inl ⟨e7, rfl, h.symm⟩
  simp only at h
  replace h := bind_eq_ok_inv h
  obtain ⟨store1, hstore1, h⟩ := h
  replace h := bind_eq_ok_inv h
  obtain ⟨store2, hstore2, h⟩ := h
  right
  have c1 := commit_kem_step _ _ _ _ hstore1
  have c2 := commit_one_time_step _ _ _ hstore2
  rcases replay with _ | fp
  · simp only [ok.injEq] at h
    exact ⟨pt, store2, rfl, ⟨store1, store2, c1, c2, rfl⟩, h.symm⟩
  · simp only at h
    replace h := bind_eq_ok_inv h
    obtain ⟨count, hcount, h⟩ := h
    replace h := bind_eq_ok_inv h
    obtain ⟨u, hu, h⟩ := h
    replace h := bind_eq_ok_inv h
    obtain ⟨seen, hseen, h⟩ := h
    simp only [ok.injEq] at h
    have hlt : count < lifecycle.MAX_LAST_RESORT_SEEN := by
      unfold massert at hu; split at hu <;> simp_all
    exact ⟨pt, _, rfl, ⟨store1, store2, c1, c2, count, seen, hcount, hlt, hseen, rfl⟩, h.symm⟩

/-! ## The inner receive refined, and the whole call -/

open Tacenta.UnitLifecycleT3 (StepRefines DhCodecOf ResultRefines)
open Tacenta.UnitLifecycleDecryptRatchetT3 (DecryptOracleOf DecryptRatchetAgreements)
open Tacenta.UnitLifecycleDecryptRunBounds (CounterHeadroom DecryptRatchetRunInputs)

/-- A draw taken by `random32` is the head of the oracle's list. -/
theorem random32_draws {o o' : Model.Lifecycle.Oracle} {c : Model.Lifecycle.Key}
    (h : Model.Lifecycle.random32 o = some (c, o')) : o.draws = c :: o'.draws := by
  unfold Model.Lifecycle.random32 Model.Lifecycle.takeDraw at h
  cases hd : o.draws with
  | nil => simp [hd] at h
  | cons d rest =>
      simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- **The `decrypt_ratchet` refinement applies to the inner call**: at the intermediate session, under the
boundary records and laws `decrypt_ratchet_refines_of_invariant` takes, the laws `DhPublicValid`,
`OptionEqU64Shape` and `DivCeilValue`, the trace equation and the run's inputs at `responderModelOf`,
`decrypt_ratchet` returns and its result, successor and draws refine `Model.Lifecycle.decryptRatchet` at
`responderModelOf dh p`.  The invariant, the ceilings and the relation are derived, not taken. -/
theorem responder_prepared_decrypt_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (p : ResponderPreparedParts our store msg) (rng : R)
    (htrace : trace rng = oracle.draws)
    (inputs : DecryptRatchetRunInputs view oracle trace p.session (responderModelOf dh p) p.message rng) :
    ∃ inner,
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng p.session p.message rng = ok inner ∧
      StepRefines trace dh oracle.braidKem inner
        (Model.Lifecycle.decryptRatchet view oracle (responderModelOf dh p) (sliceOf p.message)) :=
  Tacenta.UnitLifecycleDecryptRunBounds.decrypt_ratchet_refines_of_invariant rngCore cryptoRng trace dh
    view oracle oracleOf codec contracts agreements p.session (responderModelOf dh p) p.message rng
    (responder_prepared_invariant hpub hoeq hdiv contracts.braid.headerLen p)
    (sessionRefines_responder_prepared agreements.erasure agreements.kemLen
      (Tacenta.UnitLifecycleT3.braid_kdf_contracts_of_session agreements.hmac agreements.hkdf).2
      contracts.braid.zeroizingArray hdiv dh p)
    (counterHeadroom_responder_prepared p) htrace inputs

/-- **`establish_responder` over every input, with the inner receive refined.**  For every identity, prekey
store, initial message and source of randomness, under the hypotheses of
`responder_prepared_decrypt_refines` (the run's inputs asked of the parts the call reaches the inner receive
with), every return is one of:
* a refusal before the inner receive (`PrepareRefusal`), the store and the random source as given;
* an inner refusal: the inner step refines the model's `decryptRatchet` at `responderModelOf dh p` (so the
  error maps to the model's, and the model keeps its session), the store as given, and the random source
  either unchanged in its draws or one draw shorter;
* an inner success: the step refines the model's, the store is `ResponderCommit` of the message's
  identifiers, and exactly one draw was taken. -/
theorem establish_responder_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (hpub : DhPublicValid)
    (hoeq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (hdiv : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (msg : Slice U8) (rng : R)
    (out : core.result.Result (lifecycle.Session × alloc.vec.Vec U8) lifecycle.Error ×
      lifecycle.PrekeyStore × R)
    (h : lifecycle.establish_responder rngCore cryptoRng our store msg rng = ok out)
    (htrace : trace rng = oracle.draws)
    (hinputs : ∀ p : ResponderPreparedParts our store msg,
      DecryptRatchetRunInputs view oracle trace p.session (responderModelOf dh p) p.message rng) :
    (∃ e, PrepareRefusal e ∧ out = (core.result.Result.Err e, store, rng)) ∨
    ∃ (p : ResponderPreparedParts our store msg)
      (inner : core.result.Result (alloc.vec.Vec U8) lifecycle.Error × lifecycle.Session × R),
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng p.session p.message rng = ok inner ∧
      StepRefines trace dh oracle.braidKem inner
        (Model.Lifecycle.decryptRatchet view oracle (responderModelOf dh p) (sliceOf p.message)) ∧
      ((∃ e, inner.1 = core.result.Result.Err e ∧
          out = (core.result.Result.Err e, store, inner.2.2) ∧
          (trace inner.2.2 = trace rng ∨ ∃ d, trace rng = d :: trace inner.2.2)) ∨
       (∃ pt store', inner.1 = core.result.Result.Ok pt ∧
          ResponderCommit store p.decoded.kem_prekey_id p.decoded.one_time_prekey_id p.lastResort
            p.replay store' ∧
          out = (core.result.Result.Ok (inner.2.1, pt), store', inner.2.2) ∧
          ∃ d, trace rng = d :: trace inner.2.2)) := by
  rcases establish_responder_cases rngCore cryptoRng our store msg rng out h with hpre | ⟨p, inner, hinner, hrest⟩
  · exact Or.inl hpre
  obtain ⟨inner', hinner', hstep⟩ := responder_prepared_decrypt_refines rngCore cryptoRng trace dh view
    oracle oracleOf codec contracts agreements hpub hoeq hdiv p rng htrace (hinputs p)
  rw [hinner] at hinner'
  cases hinner'
  refine Or.inr ⟨p, inner, hinner, hstep, ?_⟩
  have hdraws := hstep.draws
  obtain ⟨hor, hsucc⟩ := decryptRatchet_oracle view oracle (responderModelOf dh p) (sliceOf p.message)
  rcases hrest with ⟨e, he, hout⟩ | ⟨pt, store', hpt, hcommit, hout⟩
  · refine Or.inl ⟨e, he, hout, ?_⟩
    rcases hor with hor | ⟨c, hc⟩
    · left; rw [hdraws, hor, htrace]
    · right; exact ⟨c, by rw [htrace, hdraws, random32_draws hc]⟩
  · refine Or.inr ⟨pt, store', hpt, hcommit, hout, ?_⟩
    have hres := hstep.result
    rw [hpt] at hres
    cases hm : (Model.Lifecycle.decryptRatchet view oracle (responderModelOf dh p)
        (sliceOf p.message)).result with
    | error r => rw [hm] at hres; exact absurd hres (by simp [ResultRefines])
    | ok b =>
        obtain ⟨c, hc⟩ := hsucc b hm
        exact ⟨c, by rw [htrace, hdraws, random32_draws hc]⟩

/-! ## The model's initial decoder inverts its encoder -/

/-- Reading four big-endian bytes back gives the value written. -/
theorem readBe32_be32 (n : UInt32) (rest : List UInt8) :
    Model.Messages.readBe32 (Model.Messages.be32 n ++ rest) = some (n, rest) := by
  rw [Tacenta.SessionUnitWireT3.readBe32_of_length _ (by simp [Model.Messages.be32])]
  simp only [Model.Messages.be32, List.cons_append, List.nil_append, List.getElem!_cons_zero,
    List.getElem!_cons_succ, List.drop_succ_cons, List.drop_zero, Option.some.injEq, Prod.mk.injEq,
    and_true]
  apply UInt32.toNat.inj
  simp only [UInt32.toNat_ofNat', UInt8.toNat_toUInt32, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  have hn := n.toNat_lt
  simp only [show (24 : UInt32).toNat % 32 = 24 from rfl, show (16 : UInt32).toNat % 32 = 16 from rfl,
    show (8 : UInt32).toNat % 32 = 8 from rfl]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  omega

/-- Splitting a prefix of known length off an append. -/
theorem takeSplit_append (a b : List UInt8) :
    Model.Messages.take? a.length (a ++ b) = some (a, b) := by
  simp [Model.Messages.take?]

/-- **The model's `decodeInitial` returns the fields `encodeInitial` wrote**, for two 33-byte keys in
`EncodeEC` form with canonical key bytes and a KEM ciphertext shorter than `2^32` bytes. -/
theorem decodeInitial_encodeInitial (i e ct : List UInt8) (s o k : UInt32) (m : List UInt8)
    (hi : i.length = 33) (he : e.length = 33)
    (hic : Model.Messages.checkCurve i = some ()) (hec : Model.Messages.checkCurve e = some ())
    (hik : Model.Messages.checkKey (i.drop 1) = some ())
    (hek : Model.Messages.checkKey (e.drop 1) = some ()) (hct : ct.length < 2 ^ 32) :
    Model.Messages.decodeInitial (Model.Messages.encodeInitial i e ct s o k m) =
      some { identity := i, ephemeral := e, kemCiphertext := ct, signedPrekeyId := s, oneTimeId := o,
             kemPrekeyId := k, ratchetMessage := m } := by
  have hlen : (UInt32.ofNat ct.length).toNat = ct.length := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hct]
  have h1 := takeSplit_append i (e ++ (Model.Messages.be32 (UInt32.ofNat ct.length) ++ (ct ++
    (Model.Messages.be32 s ++ (Model.Messages.be32 o ++ (Model.Messages.be32 k ++ m))))))
  have h2 := takeSplit_append e (Model.Messages.be32 (UInt32.ofNat ct.length) ++ (ct ++
    (Model.Messages.be32 s ++ (Model.Messages.be32 o ++ (Model.Messages.be32 k ++ m)))))
  have h3 := takeSplit_append ct (Model.Messages.be32 s ++ (Model.Messages.be32 o ++ (Model.Messages.be32 k ++ m)))
  rw [hi] at h1
  rw [he] at h2
  simp only [Model.Messages.decodeInitial, Model.Messages.encodeInitial, List.append_assoc]
  simp only [Model.Messages.version, Model.Messages.typeInitial, bne_self_eq_false, Bool.or_false,
    Bool.false_eq_true, if_false]
  simp only [Option.bind_eq_bind, h1, Option.bind_some, h2, hic, hec, hik, hek, readBe32_be32, hlen, h3]
  rfl

/-! ## A message the prepare phase accepts -/

/-- The bytes of the X25519 base point, `u = 9`. -/
def basePointBytes : List UInt8 := 9 :: List.replicate 31 0

/-- The base point in `EncodeEC` form: the curve byte, then its 32 bytes. -/
def wireKey : List UInt8 := Model.Messages.ecCurveByte :: basePointBytes

theorem wireKey_length : wireKey.length = 33 := by simp [wireKey, basePointBytes]

theorem wireKey_curve : Model.Messages.checkCurve wireKey = some () := by
  simp [wireKey, Model.Messages.checkCurve]

theorem wireKey_key : Model.Messages.checkKey (wireKey.drop 1) = some () := by
  simp only [Model.Messages.checkKey,
    if_pos (show Model.Messages.canonicalKey (wireKey.drop 1) = true by decide)]

/-- The all-zero curve public key in `EncodeEC` form: canonical, and of small order. -/
def zeroWire : List UInt8 := Model.Messages.ecCurveByte :: List.replicate 32 0

/-- The initiator's ephemeral key a message carries: the base point, or with `zeroEph` the zero key. -/
def ephKey (zeroEph : Bool) : List UInt8 := if zeroEph then zeroWire else wireKey

theorem ephKey_length (b : Bool) : (ephKey b).length = 33 := by
  cases b <;> simp [ephKey, zeroWire, wireKey, basePointBytes]

theorem ephKey_curve (b : Bool) : Model.Messages.checkCurve (ephKey b) = some () := by
  cases b <;> simp [ephKey, zeroWire, wireKey, Model.Messages.checkCurve]

theorem ephKey_key (b : Bool) : Model.Messages.checkKey ((ephKey b).drop 1) = some () := by
  cases b
  · simp only [Model.Messages.checkKey,
      if_pos (show Model.Messages.canonicalKey ((ephKey false).drop 1) = true by decide)]
  · simp only [Model.Messages.checkKey,
      if_pos (show Model.Messages.canonicalKey ((ephKey true).drop 1) = true by decide)]

/-- An initial message naming signed prekey 0, no one-time curve prekey and KEM prekey 0, with the base
point as the initiator's identity key, `ephKey zeroEph` as its ephemeral key, the given KEM ciphertext and
the given ratchet frame. -/
def successBytes (zeroEph : Bool) (ct frame : Slice U8) : List UInt8 :=
  Model.Messages.encodeInitial wireKey (ephKey zeroEph) (sliceOf ct) 0 0 0 (sliceOf frame)

/-- The length of `successBytes`. -/
theorem successBytes_length (zeroEph : Bool) (ct frame : Slice U8) :
    (successBytes zeroEph ct frame).length = 84 + ct.val.length + frame.val.length := by
  have he := ephKey_length zeroEph
  simp [successBytes, Model.Messages.encodeInitial, wireKey, basePointBytes, Model.Messages.be32,
    sliceOf, he]
  omega

/-- `successBytes` fits a slice when the ciphertext and the frame are at most 4096 bytes each. -/
theorem successBytes_le (zeroEph : Bool) (ct frame : Slice U8) (hct : ct.val.length ≤ 4096)
    (hframe : frame.val.length ≤ 4096) : (successBytes zeroEph ct frame).length ≤ Usize.max := by
  rw [successBytes_length]
  have := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
  omega

/-- `successBytes` as a slice. -/
def successMessage (zeroEph : Bool) (ct frame : Slice U8) (hct : ct.val.length ≤ 4096)
    (hframe : frame.val.length ≤ 4096) : Slice U8 :=
  Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes (successBytes zeroEph ct frame)
    (successBytes_le zeroEph ct frame hct hframe)

/-- The translated `decode_initial` accepts `successMessage`, and its result is the model's decode of
those bytes. -/
theorem decode_successMessage (zeroEph : Bool) (ct frame : Slice U8) (hct : ct.val.length ≤ 4096)
    (hframe : frame.val.length ≤ 4096) :
    ∃ d, tacenta_wire.decode_initial (successMessage zeroEph ct frame hct hframe) =
        ok (core.result.Result.Ok d) ∧
      Tacenta.SessionUnitWireInitialT3.initialOf d =
        { identity := wireKey, ephemeral := ephKey zeroEph, kemCiphertext := sliceOf ct,
          signedPrekeyId := 0, oneTimeId := 0, kemPrekeyId := 0, ratchetMessage := sliceOf frame } := by
  have hmodel : Model.Messages.decodeInitialDetailed
      (sliceOf (successMessage zeroEph ct frame hct hframe)) =
      .ok { identity := wireKey, ephemeral := ephKey zeroEph, kemCiphertext := sliceOf ct,
            signedPrekeyId := 0, oneTimeId := 0, kemPrekeyId := 0, ratchetMessage := sliceOf frame } := by
    have hs : sliceOf (successMessage zeroEph ct frame hct hframe) = successBytes zeroEph ct frame :=
      Tacenta.UnitSatisfiabilityBraidStates.sliceOf_sliceOfBytes _ _
    rw [hs, Model.Messages.decodeInitialDetailed_ok_iff]
    exact decodeInitial_encodeInitial _ _ _ _ _ _ _ wireKey_length (ephKey_length zeroEph) wireKey_curve
      (ephKey_curve zeroEph) wireKey_key (ephKey_key zeroEph) (by simp [sliceOf]; omega)
  obtain ⟨r, hr, hpost⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT3.decode_initial_refines_lifecycle (successMessage zeroEph ct frame hct hframe))
  cases r with
  | Err e =>
      obtain ⟨reason, hreason⟩ := hpost
      rw [hmodel] at hreason
      cases hreason
  | Ok d =>
      rw [hmodel] at hpost
      exact ⟨d, hr, (Except.ok.inj hpost).symm⟩

/-- On a store whose replay record is empty, the last-resort check computes the fingerprint and accepts. -/
theorem replay_fresh (hmac : Tacenta.SessionUnitT1.HmacTotal) (store : lifecycle.PrekeyStore)
    (hseen : store.last_resort_seen.val = []) (kemId : U32) (sk : Array U8 32#usize) :
    ∃ fp, lifecycle.last_resort_fingerprint sk = ok fp ∧
      lifecycle.responder_replay_fingerprint store kemId sk true =
        ok (core.result.Result.Ok (some fp)) := by
  obtain ⟨fp, hfp, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.last_resort_fingerprint_no_panic hmac sk)
  refine ⟨fp, hfp, ?_⟩
  have hloop : lifecycle.responder_replay_fingerprint_loop store fp false 0#usize =
      ok (store.identity_public, store.signed_prekey_secret, store.signed_prekey_id,
        store.signed_prekey_sig, store.one_time, store.kem, store.kem_id, store.kem_sig,
        store.kem_one_time, store.previous_signed_prekey, store.previous_kem, store.next_id,
        store.last_resort_seen, store.legacy_last_resort_blocked, false) := by
    unfold lifecycle.responder_replay_fingerprint_loop
    rw [loop.eq_def]
    simp [lifecycle.responder_replay_fingerprint_loop.body, alloc.vec.Vec.len, hseen]
  have hcount : lifecycle.PrekeyStore.last_resort_seen_for
      { identity_public := store.identity_public, signed_prekey_secret := store.signed_prekey_secret,
        signed_prekey_id := store.signed_prekey_id, signed_prekey_sig := store.signed_prekey_sig,
        one_time := store.one_time, kem := store.kem, kem_id := store.kem_id, kem_sig := store.kem_sig,
        kem_one_time := store.kem_one_time, previous_signed_prekey := store.previous_signed_prekey,
        previous_kem := store.previous_kem, next_id := store.next_id,
        last_resort_seen := store.last_resort_seen,
        legacy_last_resort_blocked := store.legacy_last_resort_blocked } kemId = ok 0#usize := by
    unfold lifecycle.PrekeyStore.last_resort_seen_for lifecycle.PrekeyStore.last_resort_seen_for_loop
    rw [loop.eq_def]
    simp [lifecycle.PrekeyStore.last_resort_seen_for_loop.body, alloc.vec.Vec.len, hseen]
  unfold lifecycle.responder_replay_fingerprint
  rw [if_pos rfl, hfp, Aeneas.Std.bind_tc_ok, hloop, Aeneas.Std.bind_tc_ok]
  show (do
      let i3 ← lifecycle.PrekeyStore.last_resort_seen_for store kemId
      if i3 ≥ lifecycle.MAX_LAST_RESORT_SEEN then
        ok (core.result.Result.Err lifecycle.Error.LastResortRecordFull)
      else ok (core.result.Result.Ok (some fp))) = ok (core.result.Result.Ok (some fp))
  have hmax : ¬ (0#usize ≥ lifecycle.MAX_LAST_RESORT_SEEN) := by
    simp [lifecycle.MAX_LAST_RESORT_SEEN]
  rw [hcount, Aeneas.Std.bind_tc_ok, if_neg hmax]

/-- Two byte lists with the same image under the byte view are equal. -/
theorem map_u8_inj {l1 l2 : List U8}
    (h : l1.map Tacenta.SessionUnitBraidT3.u8 = l2.map Tacenta.SessionUnitBraidT3.u8) : l1 = l2 := by
  have hinj : Function.Injective Tacenta.SessionUnitBraidT3.u8 := by
    intro a b hab
    simp only [Tacenta.SessionUnitBraidT3.u8] at hab
    have ha := a.hBounds
    have hb := b.hBounds
    apply UScalar.eq_of_val_eq
    have := congrArg UInt8.toNat hab
    simp only [UInt8.toNat_ofNat'] at this
    have h8 : UScalarTy.U8.numBits = 8 := rfl
    rw [h8] at ha hb
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  exact (List.map_injective_iff.mpr hinj) h

/-- A `u32` whose model value is `n < 2^32` is `n`. -/
theorem u32_of_ofNat {x : U32} {n : Nat} (hn : n < 2 ^ 32) (h : UInt32.ofNat x.val = UInt32.ofNat n) :
    x.val = n := by
  have hx := x.hBounds
  have := congrArg UInt32.toNat h
  simp only [UInt32.toNat_ofNat'] at this
  have h32 : UScalarTy.U32.numBits = 32 := rfl
  rw [h32] at hx
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hn] at this
  exact this

/-- The base point's bytes as an array. -/
theorem basePoint_length : (9#u8 :: List.replicate 31 0#u8).length = (32#usize).val := by simp

/-- The X25519 base point, `u = 9`, as the array `decode_ec` returns for `wireKey`. -/
def basePoint : Array U8 32#usize := ⟨9#u8 :: List.replicate 31 0#u8, basePoint_length⟩

theorem arrayOf_basePoint : Tacenta.UnitLifecycleT3.arrayOf basePoint = basePointBytes := by decide

theorem basePoint_canonical : Tacenta.SessionUnitT1.canonicalX25519 basePoint = true := by decide

/-- What one run of the prepare phase needs from the opaque primitives beyond totality, over an
interpretation `I`: the base point decodes to a public key with those bytes, of prime order, with which
every private key agrees contributorily; a KEM key pair that decapsulates some ciphertext of at most 4096
bytes; and a value of the zeroizing one-time pool's type.  Used only to show the route's premises hold
together at one input; no result above takes it. -/
structure ResponderSuccessShape (I : Tacenta.UnitSatisfiabilityJoint.Interp) : Prop where
  key : ∃ pkb : I.PublicKeyBytes, I.dhPubFromBytes basePoint = ok pkb ∧
    I.dhPubAsBytes pkb = ok basePoint ∧ I.dhIsPrimeOrderPublic pkb = ok true ∧
    ∀ k, ∃ x, I.dhPrivAgree k pkb = ok (some x)
  kem : ∃ (kp : I.KemKeyPair) (ct : alloc.vec.Vec U8) (ss : Array U8 32#usize),
    ct.val.length ≤ 4096 ∧ I.kemDecapsulate kp (alloc.vec.Vec.deref ct) = ok (core.result.Result.Ok ss)
  oneTime : Nonempty (I.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize)))

/-- The all-zero public key's agreement refuses for every private key, over an interpretation `I`.  True of
the boundary by reading (`tacenta-core/boundary/src/dh.rs`, `agree`: a non-contributory, all-zero output is
refused; `u = 0` gives it for every scalar); not checked in Lean.  Used only to show an inner refusal
reached. -/
def ZeroKeyShape (I : Tacenta.UnitSatisfiabilityJoint.Interp) : Prop :=
  ∃ z : I.PublicKeyBytes, I.dhPubFromBytes Tacenta.UnitSatisfiabilityBraidStates.zeros32 = ok z ∧
    ∀ k, I.dhPrivAgree k z = ok none

/-- The prekey store the run is shown at: signed prekey 0, KEM key 0 used as a last-resort key, no
one-time prekey of either kind, no previous keys, an empty replay record and no legacy marker. -/
def successStore (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (z : zeroize.Zeroizing (alloc.vec.Vec (U32 × Array U8 32#usize)))
    (kp : tacenta_boundary.kem.KeyPair) : lifecycle.PrekeyStore :=
  { identity_public := pkb, signed_prekey_secret := Tacenta.UnitSatisfiabilityBraidStates.zeros32,
    signed_prekey_id := 0#u32, signed_prekey_sig := Array.repeat 64#usize 0#u8, one_time := z,
    kem := kp, kem_id := 0#u32, kem_sig := Array.repeat 64#usize 0#u8,
    kem_one_time := alloc.vec.Vec.new _, previous_signed_prekey := none, previous_kem := none,
    next_id := 1#u32, last_resort_seen := alloc.vec.Vec.new _,
    legacy_last_resort_blocked := alloc.vec.Vec.new _ }

/-- The decoded fields of `successMessage`: the three identifiers are 0, both keys are `wireKey`, the
ciphertext and the frame are the ones put in. -/
theorem successMessage_decoded (zeroEph : Bool) (ct frame : Slice U8) (hct : ct.val.length ≤ 4096)
    (hframe : frame.val.length ≤ 4096) :
    ∃ d, tacenta_wire.decode_initial (successMessage zeroEph ct frame hct hframe) =
        ok (core.result.Result.Ok d) ∧
      d.signed_prekey_id = 0#u32 ∧ d.one_time_prekey_id = 0#u32 ∧ d.kem_prekey_id = 0#u32 ∧
      sliceOf d.identity.deref = wireKey ∧ sliceOf d.ephemeral.deref = ephKey zeroEph ∧
      d.kem_ciphertext.deref = ct ∧ d.message.deref = frame := by
  obtain ⟨d, hd, hinit⟩ := decode_successMessage zeroEph ct frame hct hframe
  refine ⟨d, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg Model.Messages.Initial.signedPrekeyId hinit
    apply UScalar.eq_of_val_eq
    exact u32_of_ofNat (n := 0) (by norm_num) h
  · have h := congrArg Model.Messages.Initial.oneTimeId hinit
    apply UScalar.eq_of_val_eq
    exact u32_of_ofNat (n := 0) (by norm_num) h
  · have h := congrArg Model.Messages.Initial.kemPrekeyId hinit
    apply UScalar.eq_of_val_eq
    exact u32_of_ofNat (n := 0) (by norm_num) h
  · exact congrArg Model.Messages.Initial.identity hinit
  · exact congrArg Model.Messages.Initial.ephemeral hinit
  · have h := congrArg Model.Messages.Initial.kemCiphertext hinit
    apply Subtype.ext
    exact map_u8_inj h
  · have h := congrArg Model.Messages.Initial.ratchetMessage hinit
    apply Subtype.ext
    exact map_u8_inj h

/-- `decode_ec` of a slice with the bytes of `wireKey` returns the key `from_bytes` makes of the base
point. -/
theorem decode_ec_wireKey (s : Slice U8) (hs : sliceOf s = wireKey)
    (pkb : tacenta_boundary.dh.PublicKeyBytes)
    (hpkb : tacenta_boundary.dh.PublicKeyBytes.from_bytes basePoint = ok pkb) :
    decode_ec s = ok (some pkb) := by
  obtain ⟨r, hr, hnone, hsome⟩ := Tacenta.SessionUnitDecodeEc.session_decode_ec_characterization s
  cases r with
  | none =>
      exfalso
      rw [hs] at hnone
      rcases hnone.mp rfl with h | h | h <;> revert h <;> decide
  | some k =>
      have hk := hsome k rfl
      rw [hs] at hk
      have hk' : k = basePoint := by
        apply Subtype.ext
        apply map_u8_inj
        have := arrayOf_basePoint
        simp only [Tacenta.UnitLifecycleT3.arrayOf] at hk this
        rw [hk, this]
        decide
      subst hk'
      simp [decode_ec, hr, hpkb]

/-- `responder_shared_secret` succeeds without a one-time key when the initiator's keys pass the identity
check and every agreement with them is contributory. -/
theorem responder_shared_secret_ok (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (hkdf : Tacenta.SessionUnitSessionT1.HkdfTotal) [Tacenta.SessionUnitSessionT1.ZeroizingModel]
    (pkb : tacenta_boundary.dh.PublicKeyBytes) (hvalid : is_valid_identity_key pkb = ok true)
    (hag : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x))
    (ik sp : tacenta_boundary.dh.PrivateKey) (enc : Array U8 32#usize) :
    ∃ sec, responder_shared_secret ik sp none pkb pkb enc = ok (core.result.Result.Ok sec) := by
  obtain ⟨x1, hx1⟩ := hag sp
  obtain ⟨x2, hx2⟩ := hag ik
  obtain ⟨z1, hz1, hz1d⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz x1)
  obtain ⟨z2, hz2, hz2d⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz x2)
  obtain ⟨sh, hsh⟩ := (Tacenta.SessionUnitT1.noPanic_iff _).mp
    (Tacenta.SessionUnitSessionT1.shared_secret_no_panic hkdf x1 x2 x1 enc none)
  unfold responder_shared_secret
  simp [hvalid, core.result.Result.Insts.CoreOpsTry.branch, hx1, hx2, contributory, hz1, hz2,
    hz1d, hz2d, hsh]

/-- **The inner receive is reached**: at the real constants, under the contracts of
`establish_responder_no_panic` and `ResponderSuccessShape`, for every identity and every ratchet frame of
at most 4096 bytes there are a prekey store (with an empty replay record), an initial message and parts
for them, whose frame is the given one and whose KEM key is used as a last-resort key.  So the theorems
that quantify over `ResponderPreparedParts` are not about an empty set under those assumptions. -/
theorem responder_prepared_inhabited {R : Type} (rc : rand_core_1.RngCore R)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rc)
    (succ : ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
    (our : lifecycle.Identity) (frame : Slice U8) (hframe : frame.val.length ≤ 4096) :
    ∃ (store : lifecycle.PrekeyStore) (msg : Slice U8) (p : ResponderPreparedParts our store msg),
      p.message = frame ∧ store.last_resort_seen.val = [] ∧ p.lastResort = true := by
  let _ : Tacenta.SessionUnitSessionT1.ZeroizingModel := contracts.sessionZeroizing
  have hdh := contracts.decrypt.dhCodec
  have hz := contracts.decrypt.braid.zeroizingArray
  obtain ⟨pkb, hpkb, hbytes, hprime, hag⟩ := succ.key
  have hpkb' : tacenta_boundary.dh.PublicKeyBytes.from_bytes basePoint = ok pkb := hpkb
  have hbytes' : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok basePoint := hbytes
  have hprime' : tacenta_boundary.dh.is_prime_order_public pkb = ok true := hprime
  have hag' : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x) := hag
  obtain ⟨kp, ct, ss, hct, hdecaps⟩ := succ.kem
  have hdecaps' : tacenta_boundary.kem.decapsulate kp (alloc.vec.Vec.deref ct) =
      ok (core.result.Result.Ok ss) := hdecaps
  obtain ⟨z⟩ := succ.oneTime
  have hvalid : is_valid_identity_key pkb = ok true :=
    is_valid_identity_key_eq pkb basePoint hbytes' basePoint_canonical hprime'
  have hctlen : (alloc.vec.Vec.deref ct).val.length ≤ 4096 := by
    simpa [alloc.vec.Vec.deref] using hct
  obtain ⟨d, hd, hsid, hoid, hkid, hident, heph, hdct, hdmsg⟩ :=
    successMessage_decoded false (alloc.vec.Vec.deref ct) frame hctlen hframe
  let store := successStore pkb z kp
  -- the signed prekey
  obtain ⟨zs, hzs, hzsd⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz
    (Tacenta.UnitSatisfiabilityBraidStates.zeros32))
  have hSigned : lifecycle.responder_signed_prekey_secret store d.signed_prekey_id =
      ok (core.result.Result.Ok zs) := by
    simp [lifecycle.responder_signed_prekey_secret, store, successStore, hsid, hzs]
  have hSlot : lifecycle.responder_kem_slot store d.kem_prekey_id =
      ok (core.result.Result.Ok (lifecycle.KemKeySlot.Current, true)) := by
    simp [lifecycle.responder_kem_slot, store, successStore, hkid, core.slice.Slice.contains,
      alloc.vec.Vec.deref, alloc.vec.Vec.new]
  have hCurve : lifecycle.responder_curve_inputs d.identity.deref d.ephemeral.deref =
      ok (core.result.Result.Ok (pkb, pkb)) := by
    simp [lifecycle.responder_curve_inputs, decode_ec_wireKey _ hident pkb hpkb',
      decode_ec_wireKey _ heph pkb hpkb', hvalid]
    rfl
  have hOneTime : lifecycle.responder_one_time_key store d.one_time_prekey_id =
      ok (core.result.Result.Ok none) := by
    simp [lifecycle.responder_one_time_key, hoid, serialization.ABSENT_ID]
  have hDecaps : lifecycle.responder_decapsulate store lifecycle.KemKeySlot.Current
      d.kem_ciphertext.deref = ok (core.result.Result.Ok ss) := by
    simp [lifecycle.responder_decapsulate, store, successStore, hdct, hdecaps']
  obtain ⟨z1, hz1, hz1d⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz ss)
  obtain ⟨sp, hsp, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.private_key_from_bytes_no_panic hdh Tacenta.UnitSatisfiabilityBraidStates.zeros32)
  obtain ⟨ik, hik, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_dh_key_no_panic hdh our)
  obtain ⟨shared, hshared⟩ := responder_shared_secret_ok hz contracts.sessionHkdf pkb hvalid hag' ik sp ss
  obtain ⟨z2, hz2, hz2d⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz shared)
  obtain ⟨fp, -, hreplay⟩ := replay_fresh contracts.decrypt.triple.hmac store rfl d.kem_prekey_id shared
  obtain ⟨sl, hsl, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT1.index_full_spec contracts.decrypt.braid.rangeFullIndex shared)
  obtain ⟨rp, hrp, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.private_key_public_no_panic hdh sp)
  obtain ⟨rb, hrb, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.public_key_as_bytes_no_panic hdh rp)
  obtain ⟨triple, htriple, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitTripleT1.State.init_receiver_no_panic contracts.decrypt.triple.hkdf
      contracts.decrypt.triple.zeroizing contracts.spqrKdfInit contracts.decrypt.triple.spqrZeroize sl rb
      tacenta_ratchet.LabelSet.Tacenta)
  obtain ⟨braid, hbraid, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT1.Braid.responder_no_panic contracts.decrypt.braid.hkdf hz
      contracts.decrypt.braid.decoderNew contracts.decrypt.braid.headerLen sl)
  obtain ⟨op, hop, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_public_no_panic hdh our)
  obtain ⟨ad, had, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_no_panic hdh pkb op)
  obtain ⟨ec, hec, hecv⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT1.vecU8_clone_no_panic d.ephemeral)
  refine ⟨store, successMessage false (alloc.vec.Vec.deref ct) frame hctlen hframe,
    { decoded := d, signedSecret := zs, kemSlot := .Current, lastResort := true, peerIdentity := pkb,
      peerEphemeral := pkb, oneTime := none, kemSecret := ss, kemSecretZ := z1,
      signedBytes := Tacenta.UnitSatisfiabilityBraidStates.zeros32, signedPrekey := sp, shared := shared,
      secretZ := z2, secret := shared, replay := some fp, tripleSecret := sl, ratchetPublic := rp,
      ratchetBytes := rb, triple := triple, braidSecret := sl, braid := braid, ratchetPrivate := sp,
      ourPublic := op, identityAd := ad, ephemeralCopy := ec,
      hDecode := hd, hSigned := hSigned, hSlot := hSlot, hCurve := hCurve, hOneTime := hOneTime,
      hDecaps := hDecaps, hKemSecretZ := hz1, hSignedBytes := hzsd, hSignedPrekey := hsp,
      hShared := ⟨ik, ss, hik, hz1d, hshared⟩, hSecretZ := hz2, hSecret := hz2d, hReplay := hreplay,
      hTripleSecret := hsl, hRatchetPublic := hrp, hRatchetBytes := hrb, hTriple := htriple,
      hBraidSecret := hsl, hBraid := hbraid, hRatchetPrivate := hsp, hOurPublic := hop,
      hIdentityAd := had, hEphemeralCopy := hec }, ?_, rfl, rfl⟩
  exact hdmsg

/-! ## The outcomes are not about an empty set -/

/-- **`establish_responder` returns for every input** under the contracts and the store bound of
`establish_responder_no_panic`, so `establish_responder_cases` speaks of every input there. -/
theorem establish_responder_returns {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (msg : Slice U8) (rng : R)
    (headroom : Tacenta.UnitLifecycleT1.EstablishResponderHeadroom store) :
    ∃ out, lifecycle.establish_responder rngCore cryptoRng our store msg rng = ok out := by
  obtain ⟨out, hout, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.establish_responder_no_panic rngCore cryptoRng contracts our store msg rng
      headroom)
  exact ⟨out, hout⟩

/-- **`Decode(TooShort)` is returned, with no hypothesis, at every prekey store**: for every identity, store
and source, a message of fewer than two bytes is refused as `Decode(TooShort)`, with the store and the source
as given.  A store value is exhibited only under `ResponderSuccessShape` (`responder_prepared_inhabited`). -/
theorem establish_responder_short_message_refused {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (msg : Slice U8) (rng : R)
    (hshort : msg.val.length < 2) :
    lifecycle.establish_responder rngCore cryptoRng our store msg rng =
      ok (core.result.Result.Err (lifecycle.Error.Decode tacenta_wire.DecodeError.TooShort), store, rng) := by
  have hlt : Slice.len msg < 2#usize := by
    simp only [Slice.len]
    scalar_tac
  simp [lifecycle.establish_responder, tacenta_wire.decode_initial, hlt]

/-- **Once the prepare phase has succeeded, the call is the inner receive followed by the commit**: for
every parts value `p` of an input (so for every input that reaches the inner receive), `establish_responder`
on that input equals `decrypt_ratchet` on `p.session` and `p.message`, then, on a refusal, that refusal with
the store as given, and on a success, the commit `ResponderCommit` describes.  So an input with parts is
never refused before the inner receive, and the call succeeds exactly when the inner receive does and the
commit returns.  Hypothesis-free. -/
theorem establish_responder_at_parts {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R) (p : ResponderPreparedParts our store msg) (rng : R) :
    lifecycle.establish_responder rngCore cryptoRng our store msg rng = (do
      let (r, session, rng1) ←
        lifecycle.Session.decrypt_ratchet rngCore cryptoRng p.session p.message rng
      match r with
      | core.result.Result.Err e => ok (core.result.Result.Err e, store, rng1)
      | core.result.Result.Ok pt => do
        let store1 ← if p.lastResort then ok store else do
          let (_, s) ← lifecycle.PrekeyStore.take_one_time_kem store p.decoded.kem_prekey_id
          ok s
        let store2 ← if p.decoded.one_time_prekey_id != serialization.ABSENT_ID then do
          let (_, s) ← lifecycle.PrekeyStore.take_one_time store1 p.decoded.one_time_prekey_id
          ok s
          else ok store1
        match p.replay with
        | none => ok (core.result.Result.Ok (session, pt), store2, rng1)
        | some fp => do
          let i ← lifecycle.PrekeyStore.last_resort_seen_for store2 p.decoded.kem_prekey_id
          massert (i < lifecycle.MAX_LAST_RESORT_SEEN)
          let v ← alloc.vec.Vec.push store2.last_resort_seen (p.decoded.kem_prekey_id, fp)
          ok (core.result.Result.Ok (session, pt), { store2 with last_resort_seen := v }, rng1)) := by
  obtain ⟨ik, enc, hik, henc, hss⟩ := p.hShared
  have hrp := p.hRatchetPrivate
  rw [p.ratchetPrivate_eq] at hrp
  have hbr := p.hBraid
  rw [p.braidSecret_eq] at hbr
  unfold lifecycle.establish_responder
  rw [p.hDecode]
  simp only [Aeneas.Std.bind_tc_ok, p.hSigned, p.hSlot, core.result.Result.Insts.CoreOpsTry.branch,
    Tacenta.UnitLifecycleT1.copy_bool_eq]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, p.hCurve, p.hOneTime, core.result.Result.Insts.CoreOpsTry.branch]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, p.hDecaps, p.hKemSecretZ, p.hSignedBytes, p.hSignedPrekey,
    core.result.Result.Insts.CoreOpsTry.branch]
  rcases hot : p.oneTime with _ | otk <;> rw [hot] at hss <;>
  · simp only [hik, henc, hss, Aeneas.Std.bind_tc_ok, p.hSecretZ, p.hSecret, p.hReplay,
      core.result.Result.Insts.CoreOpsTry.branch]
    have hts := p.hTripleSecret
    simp only [fullSlice] at hts
    simp only [hts, p.hRatchetPublic, p.hRatchetBytes, p.hTriple, hbr, p.hOurPublic, p.hIdentityAd,
      p.hEphemeralCopy, Aeneas.Std.bind_tc_ok, ResponderPreparedParts.session,
      ResponderPreparedParts.message, p.ratchetPrivate_eq]
    congr 1
    funext x
    rcases x with ⟨r, session, rng1⟩
    rcases r with pt | e <;> rfl

/-- **`UnknownPrekeyId` is returned, with no hypothesis, at every store of this shape**: for every identity,
source, ciphertext and frame of at most 4096 bytes each, and every store whose signed prekey identifier is
not 0 and that holds no previous signed prekey (a store value is exhibited only under
`ResponderSuccessShape`), `successMessage` (which names signed prekey 0) is refused as `UnknownPrekeyId`, with
the store and the source as given. -/
theorem establish_responder_unknown_prekey_refused {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (rng : R) (ct frame : Slice U8)
    (hct : ct.val.length ≤ 4096) (hframe : frame.val.length ≤ 4096)
    (hid : store.signed_prekey_id ≠ 0#u32) (hprev : store.previous_signed_prekey = none) :
    lifecycle.establish_responder rngCore cryptoRng our store (successMessage false ct frame hct hframe) rng =
      ok (core.result.Result.Err lifecycle.Error.UnknownPrekeyId, store, rng) := by
  obtain ⟨d, hd, hsid, -⟩ := successMessage_decoded false ct frame hct hframe
  have hne : ¬ (d.signed_prekey_id = store.signed_prekey_id) := by
    rw [hsid]; exact fun h => hid h.symm
  have hs : lifecycle.responder_signed_prekey_secret store d.signed_prekey_id =
      ok (core.result.Result.Err lifecycle.Error.UnknownPrekeyId) := by
    simp [lifecycle.responder_signed_prekey_secret, hne, hprev]
  unfold lifecycle.establish_responder
  rw [hd]
  simp only [Aeneas.Std.bind_tc_ok, hs, core.result.Result.Insts.CoreOpsTry.branch]
  rfl

/-- **`LegacyLastResortRecord` is returned at every store of this shape**, under the zeroizing round trip
only: for every identity, source, ciphertext and frame, and every store whose signed prekey identifier and
KEM key identifier are 0 and whose legacy marker lists 0 (a store value is exhibited only under
`ResponderSuccessShape`), `successMessage` is refused as `LegacyLastResortRecord`, with the store
and the source as given. -/
theorem establish_responder_legacy_refused {R : Type}
    (hz : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip)
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (rng : R) (ct frame : Slice U8)
    (hct : ct.val.length ≤ 4096) (hframe : frame.val.length ≤ 4096)
    (hsid : store.signed_prekey_id = 0#u32) (hkid : store.kem_id = 0#u32)
    (hlegacy : (0#u32) ∈ store.legacy_last_resort_blocked.val) :
    lifecycle.establish_responder rngCore cryptoRng our store (successMessage false ct frame hct hframe) rng =
      ok (core.result.Result.Err lifecycle.Error.LegacyLastResortRecord, store, rng) := by
  obtain ⟨d, hd, hdsid, -, hdkid, -⟩ := successMessage_decoded false ct frame hct hframe
  obtain ⟨zs, hzs, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz store.signed_prekey_secret)
  have hs : lifecycle.responder_signed_prekey_secret store d.signed_prekey_id =
      ok (core.result.Result.Ok zs) := by
    simp [lifecycle.responder_signed_prekey_secret, hdsid, hsid, hzs]
  have hcontains : core.slice.Slice.contains core.cmp.PartialEqU32
      (alloc.vec.Vec.deref store.legacy_last_resort_blocked) 0#u32 = ok true := by
    simp only [core.slice.Slice.contains, alloc.vec.Vec.deref]
    generalize store.legacy_last_resort_blocked.val = l at hlegacy
    induction l with
    | nil => simp at hlegacy
    | cons x xs ih =>
      by_cases hx : x = 0#u32
      · subst hx; simp [List.anyM]; rfl
      · have hxs : (0#u32) ∈ xs := by
          rcases List.mem_cons.mp hlegacy with h | h
          · exact absurd h.symm hx
          · exact h
        have hne : ¬ (0#u32 = x) := fun h => hx h.symm
        simp [List.anyM, hne, ih hxs]
  have hk : lifecycle.responder_kem_slot store d.kem_prekey_id =
      ok (core.result.Result.Err lifecycle.Error.LegacyLastResortRecord) := by
    simp [lifecycle.responder_kem_slot, hdkid, hkid, hcontains]
  unfold lifecycle.establish_responder
  rw [hd]
  simp only [Aeneas.Std.bind_tc_ok, hs, hk, core.result.Result.Insts.CoreOpsTry.branch]
  rfl


/-- The generated array equality on 32-byte arrays decides equality. -/
theorem array_eq_decide (a b : Array U8 32#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a = b)) := by
  have key : ∀ l1 l2 : List U8, l1.length = l2.length →
      List.allM (fun (x : U8 × U8) => (ok (decide (x.1.val = x.2.val)) : Result Bool))
        (List.zip l1 l2) = ok (decide (l1 = l2)) := by
    intro l1
    induction l1 with
    | nil => intro l2 h; cases l2 with
      | nil => rfl
      | cons _ _ => simp at h
    | cons x xs ih =>
      intro l2 h
      cases l2 with
      | nil => simp at h
      | cons y ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h
        by_cases hxy : x = y
        · subst hxy
          simp [List.allM, ih ys h]
        · have hv : x.val ≠ y.val := fun h' => hxy (UScalar.eq_of_val_eq h')
          simp [List.allM, hv, hxy]
          rfl
  have hiff : decide (a = b) = decide (a.val = b.val) := by
    by_cases h : a = b
    · subst h; simp
    · have : a.val ≠ b.val := fun h' => h (Subtype.ext h')
      simp [h, this]
  unfold core.array.equality.PartialEqArray.eq
  have hl : a.length = b.length := by simp
  rw [if_pos hl, hiff]
  have hlen : a.val.length = b.val.length := by simp
  generalize a.val = l1 at hlen ⊢
  generalize b.val = l2 at hlen ⊢
  simp only [core.cmp.PartialEqU8]
  have := key l1 l2 hlen
  simp at this ⊢
  exact this


/-- The replay loop over a record none of whose fingerprints is `fp` reports no replay. -/
theorem replay_loop_absent (store : lifecycle.PrekeyStore) (fp : Array U8 32#usize)
    (habsent : ∀ e ∈ store.last_resort_seen.val, e.2 ≠ fp) :
    lifecycle.responder_replay_fingerprint_loop store fp false 0#usize ⦃ fun r =>
      r = (store.identity_public, store.signed_prekey_secret, store.signed_prekey_id,
        store.signed_prekey_sig, store.one_time, store.kem, store.kem_id, store.kem_sig,
        store.kem_one_time, store.previous_signed_prekey, store.previous_kem, store.next_id,
        store.last_resort_seen, store.legacy_last_resort_blocked, false) ⦄ := by
  unfold lifecycle.responder_replay_fingerprint_loop
  apply loop.spec_decr_nat
    (measure := fun q => store.last_resort_seen.val.length - q.2.val)
    (inv := fun q => q.1 = false ∧ q.2.val ≤ store.last_resort_seen.val.length)
  · rintro ⟨replayed, index⟩ ⟨hr, hi⟩
    simp only at hr hi
    change lifecycle.responder_replay_fingerprint_loop.body store fp replayed index ⦃ _ ⦄
    simp only [lifecycle.responder_replay_fingerprint_loop.body]
    split
    · rename_i hlt
      have hlt' : index.val < store.last_resort_seen.val.length := by
        simpa [alloc.vec.Vec.len] using hlt
      have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (U32 × Array U8 32#usize))
          store.last_resort_seen index = ok (store.last_resort_seen.val[index.val]'hlt') := by
        rw [alloc.vec.Vec.index_slice_index]
        obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec store.last_resort_seen index hlt')
        rw [hx, hxv]
      rw [hidx]
      simp only [Aeneas.Std.bind_tc_ok]
      try dsimp only [Aeneas.Std.uncurry]
      have hne := habsent _ (List.getElem_mem hlt')
      rw [array_eq_decide, decide_eq_false hne]
      simp only [Bool.false_eq_true, if_false, Aeneas.Std.bind_tc_ok]
      have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
      obtain ⟨i1, hi1, hi1v⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by simp; scalar_tac))
      rw [hi1]
      simp only [Aeneas.Std.bind_tc_ok, WP.spec_ok]
      refine ⟨⟨hr, by simp at hi1v ⊢; omega⟩, by simp at hi1v ⊢; omega⟩
    · simp [hr]
  · exact ⟨rfl, by simp⟩

/-- Counting a record all of whose entries name `k` gives its length. -/
theorem seen_for_loop_all (store : lifecycle.PrekeyStore) (k : U32)
    (hall : ∀ e ∈ store.last_resort_seen.val, e.1 = k) :
    lifecycle.PrekeyStore.last_resort_seen_for_loop store k 0#usize 0#usize ⦃ fun r =>
      r.val = store.last_resort_seen.val.length ⦄ := by
  unfold lifecycle.PrekeyStore.last_resort_seen_for_loop
  apply loop.spec_decr_nat
    (measure := fun q => store.last_resort_seen.val.length - q.2.val)
    (inv := fun q => q.1.val = q.2.val ∧ q.2.val ≤ store.last_resort_seen.val.length)
  · rintro ⟨count, index⟩ ⟨hc, hi⟩
    simp only at hc hi
    change lifecycle.PrekeyStore.last_resort_seen_for_loop.body store k count index ⦃ _ ⦄
    simp only [lifecycle.PrekeyStore.last_resort_seen_for_loop.body]
    split
    · rename_i hlt
      have hlt' : index.val < store.last_resort_seen.val.length := by
        simpa [alloc.vec.Vec.len] using hlt
      have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (U32 × Array U8 32#usize))
          store.last_resort_seen index = ok (store.last_resort_seen.val[index.val]'hlt') := by
        rw [alloc.vec.Vec.index_slice_index]
        obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec store.last_resort_seen index hlt')
        rw [hx, hxv]
      rw [hidx]
      simp only [Aeneas.Std.bind_tc_ok]
      try dsimp only [Aeneas.Std.uncurry]
      simp only [hall _ (List.getElem_mem hlt'), if_true]
      have hu := Tacenta.UnitHeadroomSatisfiable.usize_max_ge
      have hlenmax : store.last_resort_seen.val.length ≤ Usize.max := store.last_resort_seen.property
      obtain ⟨c1, hc1, hc1v⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := count) (y := 1#usize)
        (by simp; omega))
      obtain ⟨i1, hi1, hi1v⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := index) (y := 1#usize)
        (by simp; omega))
      rw [hc1]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hi1]
      simp only [Aeneas.Std.bind_tc_ok, WP.spec_ok]
      refine ⟨⟨by simp at hc1v hi1v ⊢; omega, by simp at hi1v ⊢; omega⟩, by simp at hi1v ⊢; omega⟩
    · rename_i hge
      simp only [WP.spec_ok]
      have : index.val = store.last_resort_seen.val.length := by
        have : ¬ index.val < store.last_resort_seen.val.length := by
          simpa [alloc.vec.Vec.len] using hge
        omega
      omega
  · exact ⟨rfl, by simp⟩

/-- A 32-byte array equals itself under the generated array equality. -/
theorem array_eq_self (a : Array U8 32#usize) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a a = ok true := by
  unfold core.array.equality.PartialEqArray.eq
  simp only [if_true]
  generalize a.val = l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.allM, core.cmp.PartialEqU8] at ih ⊢
    exact ih


/-- `decode_ec` of a slice with the bytes of `zeroWire` returns the key `from_bytes` makes of the zero
bytes. -/
theorem decode_ec_zeroWire (s : Slice U8) (hs : sliceOf s = zeroWire)
    (z : tacenta_boundary.dh.PublicKeyBytes)
    (hz : tacenta_boundary.dh.PublicKeyBytes.from_bytes Tacenta.UnitSatisfiabilityBraidStates.zeros32 =
      ok z) :
    decode_ec s = ok (some z) := by
  obtain ⟨r, hr, hnone, hsome⟩ := Tacenta.SessionUnitDecodeEc.session_decode_ec_characterization s
  cases r with
  | none =>
      exfalso
      rw [hs] at hnone
      rcases hnone.mp rfl with h | h | h <;> revert h <;> decide
  | some k =>
      have hk := hsome k rfl
      rw [hs] at hk
      have hk' : k = Tacenta.UnitSatisfiabilityBraidStates.zeros32 := by
        apply Subtype.ext
        apply map_u8_inj
        simp only [Tacenta.UnitLifecycleT3.arrayOf] at hk
        rw [hk]
        decide
      subst hk'
      simp [decode_ec, hr, hz]

/-- **`Handshake(NonContributoryAgreement)` is reached before the inner receive**: under the contracts of
`establish_responder_no_panic`, `ResponderSuccessShape` and `ZeroKeyShape`, for every identity and source
there are a store and a message whose ephemeral key is the zero key, at which the call is refused as
`Handshake(NonContributoryAgreement)` by the shared-secret step, with the store and the source as given. -/
theorem establish_responder_noncontributory_refused {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rc)
    (succ : ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
    (zk : ZeroKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
    (our : lifecycle.Identity) (rng : R) (frame : Slice U8) (hframe : frame.val.length ≤ 4096) :
    ∃ (store : lifecycle.PrekeyStore) (msg : Slice U8),
      lifecycle.establish_responder rc crc our store msg rng =
        ok (core.result.Result.Err (lifecycle.Error.Handshake SessionError.NonContributoryAgreement),
          store, rng) := by
  let _ : Tacenta.SessionUnitSessionT1.ZeroizingModel := contracts.sessionZeroizing
  have hdh := contracts.decrypt.dhCodec
  have hz := contracts.decrypt.braid.zeroizingArray
  obtain ⟨pkb, hpkb, hbytes, hprime, hag⟩ := succ.key
  have hpkb' : tacenta_boundary.dh.PublicKeyBytes.from_bytes basePoint = ok pkb := hpkb
  have hbytes' : tacenta_boundary.dh.PublicKeyBytes.as_bytes pkb = ok basePoint := hbytes
  have hprime' : tacenta_boundary.dh.is_prime_order_public pkb = ok true := hprime
  have hag' : ∀ k, ∃ x, tacenta_boundary.dh.PrivateKey.agree k pkb = ok (some x) := hag
  obtain ⟨zkey, hzkey, hzag⟩ := zk
  have hzkey' : tacenta_boundary.dh.PublicKeyBytes.from_bytes Tacenta.UnitSatisfiabilityBraidStates.zeros32 =
      ok zkey := hzkey
  have hzag' : ∀ k, tacenta_boundary.dh.PrivateKey.agree k zkey = ok none := hzag
  obtain ⟨kp, ct, ss, hct, hdecaps⟩ := succ.kem
  have hdecaps' : tacenta_boundary.kem.decapsulate kp (alloc.vec.Vec.deref ct) =
      ok (core.result.Result.Ok ss) := hdecaps
  obtain ⟨z⟩ := succ.oneTime
  have hvalid : is_valid_identity_key pkb = ok true :=
    is_valid_identity_key_eq pkb basePoint hbytes' basePoint_canonical hprime'
  have hctlen : (alloc.vec.Vec.deref ct).val.length ≤ 4096 := by
    simpa [alloc.vec.Vec.deref] using hct
  obtain ⟨d, hd, hsid, hoid, hkid, hident, heph, hdct, -⟩ :=
    successMessage_decoded true (alloc.vec.Vec.deref ct) frame hctlen hframe
  let store := successStore pkb z kp
  obtain ⟨zs, hzs, hzsd⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz
    (Tacenta.UnitSatisfiabilityBraidStates.zeros32))
  have hSigned : lifecycle.responder_signed_prekey_secret store d.signed_prekey_id =
      ok (core.result.Result.Ok zs) := by
    simp [lifecycle.responder_signed_prekey_secret, store, successStore, hsid, hzs]
  have hSlot : lifecycle.responder_kem_slot store d.kem_prekey_id =
      ok (core.result.Result.Ok (lifecycle.KemKeySlot.Current, true)) := by
    simp [lifecycle.responder_kem_slot, store, successStore, hkid, core.slice.Slice.contains,
      alloc.vec.Vec.deref, alloc.vec.Vec.new]
  have hCurve : lifecycle.responder_curve_inputs d.identity.deref d.ephemeral.deref =
      ok (core.result.Result.Ok (Prod.mk (α := tacenta_boundary.dh.PublicKeyBytes)
        (β := tacenta_boundary.dh.PublicKeyBytes) pkb zkey)) := by
    simp [lifecycle.responder_curve_inputs, decode_ec_wireKey _ hident pkb hpkb',
      decode_ec_zeroWire _ heph zkey hzkey', hvalid]
  have hOneTime : lifecycle.responder_one_time_key store d.one_time_prekey_id =
      ok (core.result.Result.Ok none) := by
    simp [lifecycle.responder_one_time_key, hoid, serialization.ABSENT_ID]
  have hDecaps : lifecycle.responder_decapsulate store lifecycle.KemKeySlot.Current
      d.kem_ciphertext.deref = ok (core.result.Result.Ok ss) := by
    simp [lifecycle.responder_decapsulate, store, successStore, hdct, hdecaps']
  obtain ⟨z1, hz1, hz1d⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz ss)
  obtain ⟨sp, hsp, -⟩ := Std.WP.spec_imp_exists
    (Tacenta.UnitLifecycleT1.private_key_from_bytes_no_panic hdh Tacenta.UnitSatisfiabilityBraidStates.zeros32)
  obtain ⟨ik, hik, -⟩ := Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_dh_key_no_panic hdh our)
  have hshared : responder_shared_secret ik sp none pkb zkey ss =
      ok (core.result.Result.Err SessionError.NonContributoryAgreement) := by
    obtain ⟨x1, hx1⟩ := hag' sp
    obtain ⟨w1, hw1, -⟩ := Std.WP.spec_imp_exists (Tacenta.SessionUnitBraidT1.zeroizing_new_spec hz x1)
    unfold responder_shared_secret
    simp [hvalid, core.result.Result.Insts.CoreOpsTry.branch, hx1, hzag', contributory, hw1,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
  refine ⟨store, successMessage true (alloc.vec.Vec.deref ct) frame hctlen hframe, ?_⟩
  unfold lifecycle.establish_responder
  rw [hd]
  simp only [Aeneas.Std.bind_tc_ok, hSigned, hSlot, core.result.Result.Insts.CoreOpsTry.branch,
    Tacenta.UnitLifecycleT1.copy_bool_eq]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, hCurve, hOneTime, core.result.Result.Insts.CoreOpsTry.branch]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, hDecaps, hz1, hzsd, hsp, hik, hz1d, hshared,
    core.result.Result.Insts.CoreOpsTry.branch]

/-! ## The premises of the composed theorem hold together -/

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real ResponderAxiom)

/-- The hypotheses of `establish_responder_refines` at one choice of every binder, the class
`DerivedKeysModel` as a `Nonempty`, the call's return as an existential, and, so that the run's inputs are
not asked of an empty set, that the call reaches the inner receive (`reaches`). -/
structure ResponderRouteHypotheses {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (our : lifecycle.Identity) (store : lifecycle.PrekeyStore) (msg : Slice U8) (rng : R) : Prop where
  oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle
  codec : DhCodecOf dh
  contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore
  derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel
  agreements : DecryptRatchetAgreements oracle.braidKem
  dhPublicValid : DhPublicValid
  optionEq : OptionEqU64Shape (@core.option.Option.Insts.CoreCmpPartialEqOption.eq)
  divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue
  returns : ∃ out, lifecycle.establish_responder rngCore cryptoRng our store msg rng = ok out
  trace_eq : trace rng = oracle.draws
  inputs : ∀ p : ResponderPreparedParts our store msg,
    DecryptRatchetRunInputs view oracle trace p.session (responderModelOf dh p) p.message rng
  reaches : Nonempty (ResponderPreparedParts our store msg)

/-- The record is the hypothesis list of `establish_responder_refines`: from it, that theorem applies to
the call's return. -/
theorem ResponderRouteHypotheses.refines {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle}
    {our : lifecycle.Identity} {store : lifecycle.PrekeyStore} {msg : Slice U8} {rng : R}
    (h : ResponderRouteHypotheses rngCore cryptoRng trace dh view oracle our store msg rng) :
    ∃ out, lifecycle.establish_responder rngCore cryptoRng our store msg rng = ok out ∧
    ((∃ e, PrepareRefusal e ∧ out = (core.result.Result.Err e, store, rng)) ∨
    ∃ (p : ResponderPreparedParts our store msg)
      (inner : core.result.Result (alloc.vec.Vec U8) lifecycle.Error × lifecycle.Session × R),
      lifecycle.Session.decrypt_ratchet rngCore cryptoRng p.session p.message rng = ok inner ∧
      StepRefines trace dh oracle.braidKem inner
        (Model.Lifecycle.decryptRatchet view oracle (responderModelOf dh p) (sliceOf p.message)) ∧
      ((∃ e, inner.1 = core.result.Result.Err e ∧
          out = (core.result.Result.Err e, store, inner.2.2) ∧
          (trace inner.2.2 = trace rng ∨ ∃ d, trace rng = d :: trace inner.2.2)) ∨
       (∃ pt store', inner.1 = core.result.Result.Ok pt ∧
          ResponderCommit store p.decoded.kem_prekey_id p.decoded.one_time_prekey_id p.lastResort
            p.replay store' ∧
          out = (core.result.Result.Ok (inner.2.1, pt), store', inner.2.2) ∧
          ∃ d, trace rng = d :: trace inner.2.2))) := by
  obtain ⟨inst⟩ := h.derivedKeys
  obtain ⟨out, hout⟩ := h.returns
  exact ⟨out, hout, establish_responder_refines rngCore cryptoRng trace dh view oracle h.oracleOf h.codec
    h.contracts h.agreements h.dhPublicValid h.optionEq h.divCeil our store msg rng out hout h.trace_eq
    h.inputs⟩

/-- The sample ratchet frame fits the bound `successMessage` takes. -/
theorem sampleMessage_le : Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage.val.length ≤ 4096 := by
  have h := congrArg List.length Tacenta.UnitLifecycleDecryptRatchetScreen.sliceOf_sampleMessage
  rw [Tacenta.UnitLifecycleDecryptRatchetScreen.sampleBytes_length] at h
  simp only [Tacenta.UnitLifecycleT3.sliceOf, List.length_map] at h
  omega

/-- **Every hypothesis of `establish_responder_refines` holds together at the real constants, at an input
that reaches the inner receive**, under the decrypt laws `DecryptJointLaws K dh` of
`UnitLifecycleDecryptScreen`, the axiom part of `EstablishResponderContracts` at the byte-stream source,
`ResponderSuccessShape` and `DhPublicValid`, all assumed: for every identity there are an oracle with
`braidKem = K`, a prekey store and an initial message carrying the sample ratchet frame of
`UnitLifecycleDecryptRatchetScreen`, at which every field of `ResponderRouteHypotheses` holds, for every
codeword view. -/
theorem responder_route_hypotheses_jointly_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (ResponderAxiom Interp.real byteRng))
    (S : ResponderSuccessShape Interp.real) (hpub : DhPublicValid) (our : lifecycle.Identity) :
    ∃ (oracle : Model.Lifecycle.Oracle) (store : lifecycle.PrekeyStore) (msg : Slice U8),
      oracle.braidKem = K ∧
      (∀ q : ResponderPreparedParts our store msg,
        q.message = Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage) ∧
      ∀ view : Model.Lifecycle.CodewordView,
        ResponderRouteHypotheses byteRng byteCrc byteTrace dh view oracle our store msg
          Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng := by
  obtain ⟨oracle, hdraws, hK, horacle⟩ :=
    Tacenta.UnitOracleDecrypt.decryptOracleOf_of_laws dh L.dhCodec L.dhAgree L.aeadOpen L.viewInjective
      (byteTrace Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng) K
  obtain ⟨k, pkb, a, hpk, hbytes, hcan, hprime⟩ := L.validKey
  obtain ⟨ad, had, hlen⟩ :=
    Std.WP.spec_imp_exists (Tacenta.UnitLifecycleT1.identity_ad_length L.dhCodec pkb pkb)
  obtain ⟨c⟩ := Tacenta.UnitSatisfiabilityRecords.responder_contracts_of_axiom_base byteRng A L.laws
  obtain ⟨store, msg, p, hpmsg, hseen, -⟩ := responder_prepared_inhabited byteRng c S our
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage sampleMessage_le
  have hmsg : ∀ q : ResponderPreparedParts our store msg,
      q.message = Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage := by
    intro q
    have h1 := q.hDecode
    rw [p.hDecode] at h1
    simp only [ok.injEq, core.result.Result.Ok.injEq] at h1
    rw [← hpmsg]
    simp only [ResponderPreparedParts.message, h1]
  refine ⟨oracle, store, msg, hK, hmsg, fun view => ?_⟩
  have h0 := Tacenta.UnitLifecycleDecryptScreen.decrypt_hypotheses_at_invReal K dh L oracle hK hdraws
    horacle k pkb a hpk hbytes hcan hprime ad had hlen view
  obtain ⟨inst⟩ := h0.derivedKeys
  exact
    { oracleOf := h0.oracleOf
      codec := h0.codec
      contracts := h0.contracts
      derivedKeys := h0.derivedKeys
      agreements := h0.agreements
      dhPublicValid := hpub
      optionEq := L.optionEq
      divCeil := c.divCeilValue
      returns := establish_responder_returns byteRng byteCrc c our store msg _
        ⟨by rw [hseen]; simp; scalar_tac⟩
      trace_eq := h0.trace_eq
      inputs := fun q =>
        { chunk := fun rc mc ct hd hc => by
            rw [hmsg q] at hd
            exact Tacenta.UnitLifecycleEstablishedDecrypt.sampleMessage_chunk view _ rc mc ct hd hc
          honest := fun mc ct hd => by
            rw [hmsg q, Tacenta.UnitLifecycleDecryptRatchetScreen.sample_decode_model] at hd
            have hmc : Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite = mc :=
              (Prod.mk.inj (Except.ok.inj hd)).1
            subst hmc
            intro c hc
            simp [Model.Lifecycle.braidMessageOf,
              Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite] at hc
          draw := h0.run.draw }
      reaches := ⟨p⟩ }

/-- **`ReplayedLastResort` is reached**: under the contracts of `establish_responder_no_panic` and
`ResponderSuccessShape`, for every identity and source there are a store whose replay record holds the
fingerprint of the handshake an initial message carries, and that message, at which the call is refused as
`ReplayedLastResort`, with the store and the source as given. -/
theorem establish_responder_replay_refused {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rc)
    (succ : ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
    (our : lifecycle.Identity) (rng : R) :
    ∃ (store : lifecycle.PrekeyStore) (msg : Slice U8),
      store.last_resort_seen.val.length = 1 ∧
      lifecycle.establish_responder rc crc our store msg rng =
        ok (core.result.Result.Err lifecycle.Error.ReplayedLastResort, store, rng) := by
  obtain ⟨store, msg, p, -, hseen, hlr⟩ :=
    responder_prepared_inhabited rc contracts succ our Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
      sampleMessage_le
  obtain ⟨-, hsome⟩ := replay_ok _ _ _ _ _ p.hReplay
  obtain ⟨fp, -, hfp⟩ := hsome hlr
  let seen : alloc.vec.Vec (U32 × Array U8 32#usize) :=
    Tacenta.UnitHeadroomSatisfiable.vecOf [(p.decoded.kem_prekey_id, fp)] (singleton_length_le _)
  let store' : lifecycle.PrekeyStore := { store with last_resort_seen := seen }
  have hSigned : lifecycle.responder_signed_prekey_secret store' p.decoded.signed_prekey_id =
      ok (core.result.Result.Ok p.signedSecret) := p.hSigned
  have hSlot : lifecycle.responder_kem_slot store' p.decoded.kem_prekey_id =
      ok (core.result.Result.Ok (p.kemSlot, p.lastResort)) := p.hSlot
  have hOneTime : lifecycle.responder_one_time_key store' p.decoded.one_time_prekey_id =
      ok (core.result.Result.Ok p.oneTime) := p.hOneTime
  have hDecaps : lifecycle.responder_decapsulate store' p.kemSlot p.decoded.kem_ciphertext.deref =
      ok (core.result.Result.Ok p.kemSecret) := p.hDecaps
  have hReplay : lifecycle.responder_replay_fingerprint store' p.decoded.kem_prekey_id p.secret true =
      ok (core.result.Result.Err lifecycle.Error.ReplayedLastResort) := by
    have hloop : lifecycle.responder_replay_fingerprint_loop store' fp false 0#usize =
        ok (store'.identity_public, store'.signed_prekey_secret, store'.signed_prekey_id,
          store'.signed_prekey_sig, store'.one_time, store'.kem, store'.kem_id, store'.kem_sig,
          store'.kem_one_time, store'.previous_signed_prekey, store'.previous_kem, store'.next_id,
          store'.last_resort_seen, store'.legacy_last_resort_blocked, true) := by
      have hidx : alloc.vec.Vec.index_usize seen 0#usize = ok (p.decoded.kem_prekey_id, fp) := by
        obtain ⟨x, hx, hxv⟩ := Std.WP.spec_imp_exists
          (alloc.vec.Vec.index_usize_spec seen 0#usize (by simp [seen, Tacenta.UnitHeadroomSatisfiable.vecOf]))
        rw [hx, hxv]
        rfl
      have hadd : (0#usize + 1#usize : Result Usize) = ok 1#usize := by
        obtain ⟨z, hz, hzv⟩ := Std.WP.spec_imp_exists (Usize.add_spec (x := 0#usize) (y := 1#usize)
          (by simp; scalar_tac))
        have : z = 1#usize := by apply UScalar.eq_of_val_eq; simp at hzv ⊢; omega
        rw [hz, this]
      have hlen : alloc.vec.Vec.len seen = 1#usize := by
        apply UScalar.eq_of_val_eq; simp [seen, alloc.vec.Vec.len, Tacenta.UnitHeadroomSatisfiable.vecOf]
      unfold lifecycle.responder_replay_fingerprint_loop
      rw [loop.eq_def]
      simp only [lifecycle.responder_replay_fingerprint_loop.body]
      have hseen' : store'.last_resort_seen = seen := rfl
      rw [hseen', hlen]
      simp only [show (0#usize : Usize) < 1#usize by decide, if_true, alloc.vec.Vec.index_slice_index,
        hidx, Aeneas.Std.bind_tc_ok, hadd]
      try dsimp only [Aeneas.Std.uncurry]
      simp only [Aeneas.Std.bind_tc_ok, array_eq_self, if_true]
      rw [loop.eq_def]
      simp only [show ¬ ((1#usize : Usize) < 1#usize) by decide, if_false]
    unfold lifecycle.responder_replay_fingerprint
    rw [if_pos rfl, hfp, Aeneas.Std.bind_tc_ok, hloop, Aeneas.Std.bind_tc_ok]
    rfl
  obtain ⟨ik, enc, hik, henc, hss⟩ := p.hShared
  refine ⟨store', msg, by simp [store', seen, Tacenta.UnitHeadroomSatisfiable.vecOf], ?_⟩
  unfold lifecycle.establish_responder
  rw [p.hDecode]
  simp only [Aeneas.Std.bind_tc_ok, hSigned, hSlot, core.result.Result.Insts.CoreOpsTry.branch,
    Tacenta.UnitLifecycleT1.copy_bool_eq]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, p.hCurve, hOneTime, core.result.Result.Insts.CoreOpsTry.branch]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, hDecaps, p.hKemSecretZ, p.hSignedBytes, p.hSignedPrekey,
    core.result.Result.Insts.CoreOpsTry.branch]
  rcases hot : p.oneTime with _ | otk <;> rw [hot] at hss <;>
  · simp only [hik, henc, hss, Aeneas.Std.bind_tc_ok, p.hSecretZ, p.hSecret, hlr, hReplay,
      core.result.Result.Insts.CoreOpsTry.branch]
    rfl

/-- The side condition of a 1024-entry record. -/
theorem full_record_length_le (e : U32 × Array U8 32#usize) :
    (List.replicate 1024 e).length ≤ 4294967295 := by
  rw [List.length_replicate]
  omega

/-- A 32-byte array other than `fp`. -/
def otherThan (fp : Array U8 32#usize) : Array U8 32#usize :=
  if fp = Tacenta.UnitSatisfiabilityBraidStates.zeros32 then Array.repeat 32#usize 1#u8
  else Tacenta.UnitSatisfiabilityBraidStates.zeros32

theorem otherThan_ne (fp : Array U8 32#usize) : otherThan fp ≠ fp := by
  unfold otherThan
  split
  · rename_i h
    subst h
    decide
  · rename_i h
    exact fun h' => h h'.symm

/-- **`LastResortRecordFull` is reached**: under the contracts of `establish_responder_no_panic` and
`ResponderSuccessShape`, for every identity and source there are a store whose replay record holds 1024
entries for the KEM key a message names (none of them that handshake's fingerprint), and that message, at
which the call is refused as `LastResortRecordFull`, with the store and the source as given. -/
theorem establish_responder_record_full_refused {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R)
    (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rc)
    (succ : ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real)
    (our : lifecycle.Identity) (rng : R) :
    ∃ (store : lifecycle.PrekeyStore) (msg : Slice U8),
      store.last_resort_seen.val.length = 1024 ∧
      lifecycle.establish_responder rc crc our store msg rng =
        ok (core.result.Result.Err lifecycle.Error.LastResortRecordFull, store, rng) := by
  obtain ⟨store, msg, p, -, hseen, hlr⟩ :=
    responder_prepared_inhabited rc contracts succ our Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
      sampleMessage_le
  obtain ⟨-, hsome⟩ := replay_ok _ _ _ _ _ p.hReplay
  obtain ⟨fp, -, hfp⟩ := hsome hlr
  let seen : alloc.vec.Vec (U32 × Array U8 32#usize) :=
    Tacenta.UnitHeadroomSatisfiable.vecOf (List.replicate 1024 (p.decoded.kem_prekey_id, otherThan fp))
      (full_record_length_le _)
  let store' : lifecycle.PrekeyStore := { store with last_resort_seen := seen }
  have hSigned : lifecycle.responder_signed_prekey_secret store' p.decoded.signed_prekey_id =
      ok (core.result.Result.Ok p.signedSecret) := p.hSigned
  have hSlot : lifecycle.responder_kem_slot store' p.decoded.kem_prekey_id =
      ok (core.result.Result.Ok (p.kemSlot, p.lastResort)) := p.hSlot
  have hOneTime : lifecycle.responder_one_time_key store' p.decoded.one_time_prekey_id =
      ok (core.result.Result.Ok p.oneTime) := p.hOneTime
  have hDecaps : lifecycle.responder_decapsulate store' p.kemSlot p.decoded.kem_ciphertext.deref =
      ok (core.result.Result.Ok p.kemSecret) := p.hDecaps
  have hseenv : store'.last_resort_seen.val = List.replicate 1024 (p.decoded.kem_prekey_id, otherThan fp) :=
    rfl
  have hReplay : lifecycle.responder_replay_fingerprint store' p.decoded.kem_prekey_id p.secret true =
      ok (core.result.Result.Err lifecycle.Error.LastResortRecordFull) := by
    obtain ⟨r, hloop, hr⟩ := Std.WP.spec_imp_exists (replay_loop_absent store' fp (by
      intro e he
      rw [hseenv] at he
      rw [(List.eq_of_mem_replicate he)]
      exact otherThan_ne fp))
    subst hr
    obtain ⟨c, hc, hcv⟩ := Std.WP.spec_imp_exists (seen_for_loop_all store' p.decoded.kem_prekey_id (by
      intro e he
      rw [hseenv] at he
      rw [(List.eq_of_mem_replicate he)]))
    have hcount : lifecycle.PrekeyStore.last_resort_seen_for store' p.decoded.kem_prekey_id = ok c := hc
    have hfull : c ≥ lifecycle.MAX_LAST_RESORT_SEEN := by
      rw [hseenv] at hcv
      simp only [List.length_replicate] at hcv
      show lifecycle.MAX_LAST_RESORT_SEEN ≤ c
      simp [lifecycle.MAX_LAST_RESORT_SEEN, UScalar.le_equiv, hcv]
    unfold lifecycle.responder_replay_fingerprint
    rw [if_pos rfl, hfp, Aeneas.Std.bind_tc_ok, hloop, Aeneas.Std.bind_tc_ok]
    show (do
        let i3 ← lifecycle.PrekeyStore.last_resort_seen_for store' p.decoded.kem_prekey_id
        if i3 ≥ lifecycle.MAX_LAST_RESORT_SEEN then
          ok (core.result.Result.Err lifecycle.Error.LastResortRecordFull)
        else ok (core.result.Result.Ok (some fp))) =
      ok (core.result.Result.Err lifecycle.Error.LastResortRecordFull)
    rw [hcount, Aeneas.Std.bind_tc_ok, if_pos hfull]
  obtain ⟨ik, enc, hik, henc, hss⟩ := p.hShared
  refine ⟨store', msg, by rw [hseenv, List.length_replicate], ?_⟩
  unfold lifecycle.establish_responder
  rw [p.hDecode]
  simp only [Aeneas.Std.bind_tc_ok, hSigned, hSlot, core.result.Result.Insts.CoreOpsTry.branch,
    Tacenta.UnitLifecycleT1.copy_bool_eq]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, p.hCurve, hOneTime, core.result.Result.Insts.CoreOpsTry.branch]
  try dsimp only [Aeneas.Std.uncurry]
  simp only [Aeneas.Std.bind_tc_ok, hDecaps, p.hKemSecretZ, p.hSignedBytes, p.hSignedPrekey,
    core.result.Result.Insts.CoreOpsTry.branch]
  rcases hot : p.oneTime with _ | otk <;> rw [hot] at hss <;>
  · simp only [hik, henc, hss, Aeneas.Std.bind_tc_ok, p.hSecretZ, p.hSecret, hlr, hReplay,
      core.result.Result.Insts.CoreOpsTry.branch]
    rfl

/-- **An inner refusal is reached, at the real constants**: under the hypotheses of
`responder_route_hypotheses_jointly_satisfiable` and `ZeroKeyShape`, at the input it builds (whose frame's
ratchet key is the all-zero key), the call reaches the inner receive, and returns the inner refusal that maps
to the model's `NonContributoryAgreement`, with the store as given. -/
theorem responder_route_inner_refusal_reachable (K : Model.Braid.Kem) (dh : DhView)
    (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (ResponderAxiom Interp.real byteRng))
    (S : ResponderSuccessShape Interp.real) (Z : ZeroKeyShape Interp.real) (hpub : DhPublicValid)
    (our : lifecycle.Identity) (view : Model.Lifecycle.CodewordView) :
    ∃ (oracle : Model.Lifecycle.Oracle) (store : lifecycle.PrekeyStore) (msg : Slice U8)
      (e : lifecycle.Error) (rng' : List U8),
      oracle.braidKem = K ∧
      ResponderRouteHypotheses byteRng byteCrc byteTrace dh view oracle our store msg
        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng ∧
      lifecycle.establish_responder byteRng byteCrc our store msg
        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng =
        ok (core.result.Result.Err e, store, rng') ∧
      Tacenta.UnitLifecycleT3.refusalOf e =
        Model.Lifecycle.Refusal.handshake Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement := by
  obtain ⟨oracle, store, msg, hK, hmsgAll, hall⟩ :=
    responder_route_hypotheses_jointly_satisfiable K dh L A S hpub our
  have H := hall view
  obtain ⟨p⟩ := H.reaches
  obtain ⟨inst⟩ := H.derivedKeys
  obtain ⟨inner, hinner, hstep⟩ := responder_prepared_decrypt_refines byteRng byteCrc byteTrace dh view
    oracle H.oracleOf H.codec H.contracts H.agreements H.dhPublicValid H.optionEq H.divCeil p
    Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng H.trace_eq (H.inputs p)
  -- the message is the sample frame
  have hmsg := hmsgAll p
  obtain ⟨z, hz, hzagree⟩ := Z
  have hz' : tacenta_boundary.dh.PublicKeyBytes.from_bytes Tacenta.UnitSatisfiabilityBraidStates.zeros32 =
      ok z := hz
  have hzag : ∀ k, tacenta_boundary.dh.PrivateKey.agree k z = ok none := hzagree
  obtain ⟨z2, hz2, hview⟩ := H.codec.fromBytes Tacenta.UnitSatisfiabilityBraidStates.zeros32
  rw [hz'] at hz2
  cases hz2
  obtain ⟨res, hres, hmap⟩ := H.oracleOf.dhAgree p.ratchetPrivate z
  rw [hzag] at hres
  cases hres
  have hdh : dh.publicKey z = Tacenta.UnitLifecycleDecryptRatchetScreen.sampleComposite.dh := by
    rw [hview]
    decide
  have hmodel : (Model.Lifecycle.decryptRatchet view oracle (responderModelOf dh p)
      (sliceOf p.message)).result =
      .error (.handshake .nonContributoryAgreement) := by
    rw [hmsg]
    unfold Model.Lifecycle.decryptRatchet
    simp only [Model.Lifecycle.agreementFailed, responderModelOf, Model.Braid.initBob,
      Tacenta.UnitLifecycleDecryptRatchetScreen.sample_decode_model, Bool.false_eq_true, if_false]
    rw [← hdh, ← hmap]
    rfl
  have hres := hstep.result
  obtain ⟨r, s', rng'⟩ := inner
  rcases r with pt | e
  · rw [hmodel] at hres
    exact absurd hres (by simp [ResultRefines])
  · refine ⟨oracle, store, msg, e, rng', hK, H, ?_, ?_⟩
    · rw [establish_responder_at_parts byteRng byteCrc p, hinner]
      rfl
    · rw [hmodel] at hres
      exact hres

/-! ### One interpretation satisfies every law the statement above takes -/

open Tacenta.UnitLifecycleEstablishedDecrypt (Interp.modelEstablished viewEstablished
  established_decrypt_laws_model)
open Tacenta.UnitLifecycleDecryptRatchetScreen (modelDecrypt_allT1 modelDecrypt_zeroizingModel) in
/-- **The decrypt laws, the axiom part of `EstablishResponderContracts`, `ResponderSuccessShape`,
`DhPublicValidShape` and `ZeroKeyShape` hold together in one interpretation**, `Interp.modelEstablished` of
`UnitLifecycleEstablishedDecrypt`, with its view, the KEM model `toyKem`, `optionEqImpl` for `Option::eq`
and the byte-stream source: the shapes of every hypothesis `responder_route_hypotheses_jointly_satisfiable`,
`responder_route_inner_refusal_reachable` and the reached refusals take (the contracts of
`establish_responder_no_panic` follow from the axiom part and the decrypt laws' `StdLaws`,
`UnitSatisfiabilityRecords.responder_contracts_of_axiom_base`).  In the substitution sense of
`UnitSatisfiabilityRecords`; not a statement that the real primitives meet them.  The model's public-key
check accepts every key, its agreement refuses only the zero key (the base point is not), and its KEM
decapsulation always returns. -/
theorem responder_route_laws_model :
    Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape Interp.modelEstablished viewEstablished
        Model.Braid.toyKem @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
      Nonempty (ResponderAxiom Interp.modelEstablished byteRng) ∧
      ResponderSuccessShape Interp.modelEstablished ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape Interp.modelEstablished ∧
      ZeroKeyShape Interp.modelEstablished := by
  obtain ⟨M, -, -, hpub, -⟩ := established_decrypt_laws_model
  refine ⟨M, ⟨?_⟩, ?_, hpub, ?_⟩
  · exact
      { decrypt := ⟨M.dhCodec, M.dhAgree, M.aeadOpen, fun _ _ _ => ⟨_, rfl⟩, M.braid, M.triple,
          M.messageKeyMaterial⟩
        dhIdentity := modelDecrypt_allT1.dhIdentity
        kemDecapsulate := modelDecrypt_allT1.kemDecapsulate
        sessionHkdf := modelDecrypt_allT1.hkdf
        sessionZeroizing := by
          have h := modelDecrypt_zeroizingModel Tacenta.UnitSatisfiabilityJoint.SessionZ
          cases h; constructor <;> assumption
        vecPop := modelDecrypt_allT1.vecPop
        divCeilValue := M.laws.divCeil }
  · refine ⟨⟨basePoint, rfl, rfl, rfl, fun k => ⟨k, ?_⟩⟩,
      ⟨(), alloc.vec.Vec.new U8, Tacenta.UnitSatisfiabilityBraidStates.zeros32, by simp, rfl⟩,
      ⟨alloc.vec.Vec.new _⟩⟩
    show ok (if basePoint.val = Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none else some k) =
      ok (some k)
    have hne : basePoint.val ≠ Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val := by decide
    simp [hne]
  · refine ⟨Tacenta.UnitSatisfiabilityBraidStates.zeros32, rfl, fun k => ?_⟩
    show (ok (if Tacenta.UnitSatisfiabilityBraidStates.zeros32.val =
        Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32.val then none else some k)) = ok none
    simp [Tacenta.UnitSatisfiabilityBraidStates.zeros32, Tacenta.UnitLifecycleDecryptRatchetScreen.zeros32]

end Tacenta.UnitLifecycleEstablishResponder

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.signed_prekey_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.signed_prekey_err

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.kem_slot_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.kem_slot_err

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.curve_inputs_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.curve_inputs_err

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.one_time_key_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.one_time_key_err

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.decapsulate_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.decapsulate_err

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.contributory_break_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.contributory_break_err

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.shared_secret_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.shared_secret_err

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.replay_err' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.replay_err

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.commit_kem_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.alloc.vec.Vec.pop]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.commit_kem_step

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.commit_one_time_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.commit_one_time_step

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.init_receiver_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.init_receiver_ok

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.braid_responder_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.braid_responder_ok

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.vecU8_clone_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.vecU8_clone_eq

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.curve_inputs_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.curve_inputs_ok

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ratchetPrivate_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ratchetPrivate_eq

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.braidSecret_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.braidSecret_eq

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ephemeralCopy_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ephemeralCopy_eq

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.fresh_decoder_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.fresh_decoder_invariant

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_checks

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responderTriple_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responderTriple_invariant

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responder_structural' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responder_structural

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responder_prepared_invariant' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responder_prepared_invariant

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.counterHeadroom_responder_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.counterHeadroom_responder_prepared

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.sessionRefines_responder_prepared' depends on axioms: [propext,
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
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.sessionRefines_responder_prepared

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.honestChunk_responder_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.honestChunk_responder_iff

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.decryptRatchet_oracle' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.decryptRatchet_oracle

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.take_one_time_kem_loop_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.take_one_time_kem_loop_frame

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.take_one_time_kem_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.alloc.vec.Vec.pop]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.take_one_time_kem_frame

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.take_one_time_loop_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.take_one_time_loop_frame

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.take_one_time_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.take_one_time_frame

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.vec_push_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.vec_push_ok

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responderCommit_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responderCommit_effects

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.replay_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.replay_ok

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_cases' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_cases

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.random32_draws' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.random32_draws

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responder_prepared_decrypt_refines' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responder_prepared_decrypt_refines

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_refines' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_refines

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.readBe32_be32' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.readBe32_be32

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.takeSplit_append' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.takeSplit_append

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.decodeInitial_encodeInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.decodeInitial_encodeInitial

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.wireKey_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.wireKey_length

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.wireKey_curve' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.wireKey_curve

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.wireKey_key' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.wireKey_key

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.ephKey_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.ephKey_length

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.ephKey_curve' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.ephKey_curve

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.ephKey_key' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.ephKey_key

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.successBytes_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.successBytes_length

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.successBytes_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.successBytes_le

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.decode_successMessage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.decode_successMessage

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.replay_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.replay_fresh

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.map_u8_inj' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.map_u8_inj

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.u32_of_ofNat' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.u32_of_ofNat

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.basePoint_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.basePoint_length

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.arrayOf_basePoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.arrayOf_basePoint

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.successMessage_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.successMessage_decoded

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.decode_ec_wireKey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.decode_ec_wireKey

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responder_shared_secret_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.agree,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responder_shared_secret_ok

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responder_prepared_inhabited' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responder_prepared_inhabited

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_returns' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_returns

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_short_message_refused' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_short_message_refused

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_at_parts' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_at_parts

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_unknown_prekey_refused' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_unknown_prekey_refused

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_legacy_refused' depends on axioms: [propext,
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
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_legacy_refused

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.array_eq_decide' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.array_eq_decide

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.replay_loop_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.replay_loop_absent

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.seen_for_loop_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.seen_for_loop_all

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.array_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.array_eq_self

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.decode_ec_zeroWire' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.decode_ec_zeroWire

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_noncontributory_refused' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_noncontributory_refused

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.refines' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.refines

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.sampleMessage_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.sampleMessage_le

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responder_route_hypotheses_jointly_satisfiable' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responder_route_hypotheses_jointly_satisfiable

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_replay_refused' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_replay_refused

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.full_record_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.full_record_length_le

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.otherThan_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.otherThan_ne

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.establish_responder_record_full_refused' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.establish_responder_record_full_refused

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responder_route_inner_refusal_reachable' depends on axioms: [propext,
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
 tacenta_session_unit.tacenta_kem.encapsulate1,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.tacenta_boundary.aead.decrypt,
 tacenta_session_unit.tacenta_boundary.aead.encrypt,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.KeyPair,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_boundary.kem.decapsulate,
 tacenta_session_unit.tacenta_boundary.kem.encapsulate,
 tacenta_session_unit.tacenta_boundary.xeddsa.verify,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.chain_start_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.tacenta_kem.EncapsState.Insts.CoreCloneClone.clone,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.Insts.CoreCloneClone.clone,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responder_route_inner_refusal_reachable

/--
info: 'Tacenta.UnitLifecycleEstablishResponder.responder_route_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleEstablishResponder.responder_route_laws_model

/--
info: Tacenta.UnitLifecycleEstablishResponder.signed_prekey_err : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (id : Aeneas.Std.U32) (e : tacenta_session_unit.lifecycle.Error),
  tacenta_session_unit.lifecycle.responder_signed_prekey_secret store id =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
    e = tacenta_session_unit.lifecycle.Error.UnknownPrekeyId
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.signed_prekey_err

/--
info: Tacenta.UnitLifecycleEstablishResponder.kem_slot_err : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (id : Aeneas.Std.U32) (e : tacenta_session_unit.lifecycle.Error),
  tacenta_session_unit.lifecycle.responder_kem_slot store id =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
    e = tacenta_session_unit.lifecycle.Error.LegacyLastResortRecord ∨
      e = tacenta_session_unit.lifecycle.Error.UnknownPrekeyId
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.kem_slot_err

/--
info: Tacenta.UnitLifecycleEstablishResponder.curve_inputs_err : ∀ (identity ephemeral : Aeneas.Std.Slice Aeneas.Std.U8)
  (e : tacenta_session_unit.lifecycle.Error),
  tacenta_session_unit.lifecycle.responder_curve_inputs identity ephemeral =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
    e = tacenta_session_unit.lifecycle.Error.BadEncoding ∨
      e = tacenta_session_unit.lifecycle.Error.Handshake tacenta_session_unit.SessionError.InvalidIdentityKey
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.curve_inputs_err

/--
info: Tacenta.UnitLifecycleEstablishResponder.one_time_key_err : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (id : Aeneas.Std.U32) (e : tacenta_session_unit.lifecycle.Error),
  tacenta_session_unit.lifecycle.responder_one_time_key store id =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
    e = tacenta_session_unit.lifecycle.Error.UnknownPrekeyId
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.one_time_key_err

/--
info: Tacenta.UnitLifecycleEstablishResponder.decapsulate_err : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (slot : tacenta_session_unit.lifecycle.KemKeySlot) (ct : Aeneas.Std.Slice Aeneas.Std.U8)
  (e : tacenta_session_unit.lifecycle.Error),
  tacenta_session_unit.lifecycle.responder_decapsulate store slot ct =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
    e = tacenta_session_unit.lifecycle.Error.Kem ∨ e = tacenta_session_unit.lifecycle.Error.UnknownPrekeyId
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.decapsulate_err

/--
info: @Tacenta.UnitLifecycleEstablishResponder.contributory_break_err : ∀ {T : Type}
  {o : Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize)}
  {r : Aeneas.Std.core.result.Result (Aeneas.Std.Array Aeneas.Std.U8 32#usize) tacenta_session_unit.SessionError}
  {res : Aeneas.Std.core.result.Result Aeneas.Std.core.convert.Infallible tacenta_session_unit.SessionError}
  {e : tacenta_session_unit.SessionError},
  tacenta_session_unit.contributory o = Aeneas.Std.Result.ok r →
    Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch r =
        Aeneas.Std.Result.ok (Aeneas.Std.core.ops.control_flow.ControlFlow.Break res) →
      Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual T
            (Aeneas.Std.core.convert.FromSame tacenta_session_unit.SessionError) res =
          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
        e = tacenta_session_unit.SessionError.NonContributoryAgreement
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.contributory_break_err

/--
info: Tacenta.UnitLifecycleEstablishResponder.shared_secret_err : ∀
  (ik sp : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (otk : Option tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
  (pi pe : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (enc : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  (e : tacenta_session_unit.SessionError),
  tacenta_session_unit.responder_shared_secret ik sp otk pi pe enc =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
    e = tacenta_session_unit.SessionError.InvalidIdentityKey ∨
      e = tacenta_session_unit.SessionError.NonContributoryAgreement
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.shared_secret_err

/--
info: Tacenta.UnitLifecycleEstablishResponder.replay_err : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (kemId : Aeneas.Std.U32) (sk : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (lastResort : Bool)
  (e : tacenta_session_unit.lifecycle.Error),
  tacenta_session_unit.lifecycle.responder_replay_fingerprint store kemId sk lastResort =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e) →
    e = tacenta_session_unit.lifecycle.Error.ReplayedLastResort ∨
      e = tacenta_session_unit.lifecycle.Error.LastResortRecordFull
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.replay_err

/--
info: Tacenta.UnitLifecycleEstablishResponder.commit_kem_step : ∀ (b : Bool)
  (store store1 : tacenta_session_unit.lifecycle.PrekeyStore) (kemId : Aeneas.Std.U32),
  (if b = true then Aeneas.Std.Result.ok store
      else do
        let (_, s) ← store.take_one_time_kem kemId
        Aeneas.Std.Result.ok s) =
      Aeneas.Std.Result.ok store1 →
    if b = true then store1 = store else ∃ x, store.take_one_time_kem kemId = Aeneas.Std.Result.ok (x, store1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.commit_kem_step

/--
info: Tacenta.UnitLifecycleEstablishResponder.commit_one_time_step : ∀ (id : Aeneas.Std.U32)
  (store1 store2 : tacenta_session_unit.lifecycle.PrekeyStore),
  (if (id != tacenta_session_unit.serialization.ABSENT_ID) = true then do
        let (_, s) ← store1.take_one_time id
        Aeneas.Std.Result.ok s
      else Aeneas.Std.Result.ok store1) =
      Aeneas.Std.Result.ok store2 →
    if (id != tacenta_session_unit.serialization.ABSENT_ID) = true then
      ∃ b, store1.take_one_time id = Aeneas.Std.Result.ok (b, store2)
    else store2 = store1
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.commit_one_time_step

/--
info: Tacenta.UnitLifecycleEstablishResponder.init_receiver_ok : ∀ (sk : Aeneas.Std.Slice Aeneas.Std.U8)
  (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (t : tacenta_session_unit.tacenta_triple.State),
  tacenta_session_unit.tacenta_triple.State.init_receiver sk a tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
      Aeneas.Std.Result.ok t →
    ∃ rk prk c1 c2, t = Tacenta.UnitLifecycleEstablishResponder.responderTriple a rk prk c1 c2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.init_receiver_ok

/--
info: Tacenta.UnitLifecycleEstablishResponder.braid_responder_ok : ∀ (s : Aeneas.Std.Slice Aeneas.Std.U8)
  (b : tacenta_session_unit.tacenta_braid.Braid),
  tacenta_session_unit.tacenta_braid.Braid.responder s = Aeneas.Std.Result.ok b →
    ∃ auth d,
      tacenta_session_unit.tacenta_braid.hdr_decoder = Aeneas.Std.Result.ok d ∧
        b = { state := tacenta_session_unit.tacenta_braid.State.NoHeaderReceived 1#u64 auth d }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.braid_responder_ok

/--
info: Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok : ∀ (d : tacenta_session_unit.tacenta_erasure.Decoder),
  tacenta_session_unit.tacenta_braid.hdr_decoder = Aeneas.Std.Result.ok d →
    ∃ hv n needed,
      tacenta_session_unit.tacenta_kem.HEADER_LEN = Aeneas.Std.Result.ok hv ∧
        hv + tacenta_session_unit.tacenta_braid.MAC_LEN = Aeneas.Std.Result.ok n ∧
          ↑n = ↑hv + 32 ∧
            tacenta_session_unit.tacenta_erasure.chunk_count n = Aeneas.Std.Result.ok needed ∧
              d =
                { size := n, needed := needed,
                  «have» := Aeneas.Std.alloc.vec.Vec.new tacenta_session_unit.tacenta_erasure.Chunk }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_ok

/--
info: @Tacenta.UnitLifecycleEstablishResponder.vecU8_clone_eq : ∀ {v v' : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8},
  Aeneas.Std.alloc.vec.CloneVec.clone Aeneas.Std.core.clone.CloneU8 v = Aeneas.Std.Result.ok v' → v' = v
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.vecU8_clone_eq

/--
info: Tacenta.UnitLifecycleEstablishResponder.curve_inputs_ok : ∀ (identity ephemeral : Aeneas.Std.Slice Aeneas.Std.U8)
  (a b : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
  tacenta_session_unit.lifecycle.responder_curve_inputs identity ephemeral =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (a, b)) →
    tacenta_session_unit.decode_ec identity = Aeneas.Std.Result.ok (some a) ∧
      tacenta_session_unit.is_valid_identity_key a = Aeneas.Std.Result.ok true ∧
        tacenta_session_unit.decode_ec ephemeral = Aeneas.Std.Result.ok (some b)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.curve_inputs_ok

/--
info: @Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ratchetPrivate_eq : ∀
  {our : tacenta_session_unit.lifecycle.Identity} {store : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg), p.ratchetPrivate = p.signedPrekey
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ratchetPrivate_eq

/--
info: @Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.braidSecret_eq : ∀
  {our : tacenta_session_unit.lifecycle.Identity} {store : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg), p.braidSecret = p.tripleSecret
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.braidSecret_eq

/--
info: @Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ephemeralCopy_eq : ∀
  {our : tacenta_session_unit.lifecycle.Identity} {store : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
  p.ephemeralCopy = p.decoded.ephemeral
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ephemeralCopy_eq

/--
info: Tacenta.UnitLifecycleEstablishResponder.fresh_decoder_invariant : ∀ (n needed : Aeneas.Std.Usize),
  tacenta_session_unit.tacenta_erasure.chunk_count n = Aeneas.Std.Result.ok needed →
    ↑needed ≤ 65536 →
      { size := n, needed := needed,
            «have» := Aeneas.Std.alloc.vec.Vec.new tacenta_session_unit.tacenta_erasure.Chunk }.invariant =
        Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.fresh_decoder_invariant

/--
info: Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_checks : Tacenta.SessionUnitDecoderBound.DivCeilValue →
  Tacenta.SessionUnitBraidT1.HeaderLenTotal →
    ∀ (d : tacenta_session_unit.tacenta_erasure.Decoder),
      tacenta_session_unit.tacenta_braid.hdr_decoder = Aeneas.Std.Result.ok d →
        d.invariant = Aeneas.Std.Result.ok true ∧
          (do
              let i ← tacenta_session_unit.tacenta_kem.HEADER_LEN
              let i1 ← i + tacenta_session_unit.tacenta_braid.MAC_LEN
              tacenta_session_unit.tacenta_braid.decoder_sized d i1) =
            Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.hdr_decoder_checks

/--
info: Tacenta.UnitLifecycleEstablishResponder.responderTriple_invariant : ∀
  (a rk prk c1 c2 : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.SessionUnitT1.canonicalX25519 a = true →
    (Tacenta.UnitLifecycleEstablishResponder.responderTriple a rk prk c1 c2).invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responderTriple_invariant

/--
info: @Tacenta.UnitLifecycleEstablishResponder.responder_structural : ∀ {our : tacenta_session_unit.lifecycle.Identity}
  {store : tacenta_session_unit.lifecycle.PrekeyStore} {msg : Aeneas.Std.Slice Aeneas.Std.U8},
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
        @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
      ∀ (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
        p.session.structural_invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responder_structural

/--
info: @Tacenta.UnitLifecycleEstablishResponder.responder_prepared_invariant : ∀
  {our : tacenta_session_unit.lifecycle.Identity} {store : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8},
  Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
    Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
        @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
      Tacenta.SessionUnitDecoderBound.DivCeilValue →
        Tacenta.SessionUnitBraidT1.HeaderLenTotal →
          ∀ (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
            p.session.invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responder_prepared_invariant

/--
info: @Tacenta.UnitLifecycleEstablishResponder.counterHeadroom_responder_prepared : ∀
  {our : tacenta_session_unit.lifecycle.Identity} {store : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom p.session
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.counterHeadroom_responder_prepared

/--
info: @Tacenta.UnitLifecycleEstablishResponder.sessionRefines_responder_prepared : ∀
  {our : tacenta_session_unit.lifecycle.Identity} {store : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8},
  Tacenta.SessionUnitBraidT3.ErasureAgrees →
    ∀ {K : Model.Braid.Kem},
      Tacenta.SessionUnitBraidT3.KemLenAgrees K →
        Tacenta.SessionUnitBraidT3.BraidHkdfAgrees →
          Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
            Tacenta.SessionUnitDecoderBound.DivCeilValue →
              ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
                (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
                Tacenta.UnitLifecycleT3.SessionRefines dh K p.session
                  (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.sessionRefines_responder_prepared

/--
info: @Tacenta.UnitLifecycleEstablishResponder.honestChunk_responder_iff : ∀ {our : tacenta_session_unit.lifecycle.Identity}
  {store : tacenta_session_unit.lifecycle.PrekeyStore} {msg : Aeneas.Std.Slice Aeneas.Std.U8}
  (dh : Tacenta.UnitLifecycleT3.DhView)
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg) (msg' : Model.Braid.Msg),
  Tacenta.SessionUnitBraidT3.HonestChunk (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p).braid msg' ↔
    ∀ (mc : Model.Braid.Chunk),
      msg'.data = some mc →
        msg'.epoch = 1 →
          msg'.type = Model.Braid.MsgType.hdr → List.length mc.source = Model.Braid.headerSize + Model.Braid.macSize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.honestChunk_responder_iff

/--
info: Tacenta.UnitLifecycleEstablishResponder.decryptRatchet_oracle : ∀ (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (session : Model.Lifecycle.Session) (message : Model.Lifecycle.Bytes),
  ((Model.Lifecycle.decryptRatchet view oracle session message).oracle = oracle ∨
      ∃ c,
        Model.Lifecycle.random32 oracle =
          some (c, (Model.Lifecycle.decryptRatchet view oracle session message).oracle)) ∧
    ∀ (pt : Model.Lifecycle.Bytes),
      (Model.Lifecycle.decryptRatchet view oracle session message).result = Except.ok pt →
        ∃ c,
          Model.Lifecycle.random32 oracle =
            some (c, (Model.Lifecycle.decryptRatchet view oracle session message).oracle)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.decryptRatchet_oracle

/--
info: Tacenta.UnitLifecycleEstablishResponder.take_one_time_kem_loop_frame : ∀
  (store : tacenta_session_unit.lifecycle.PrekeyStore) (id : Aeneas.Std.U32) (index : Aeneas.Std.Usize),
  ↑index ≤ (↑store.kem_one_time).length →
    Aeneas.Std.WP.spec (store.take_one_time_kem_loop id index) fun r =>
      ∃ found,
        r =
          (store.identity_public, store.signed_prekey_secret, store.signed_prekey_id, store.signed_prekey_sig,
            store.one_time, store.kem, store.kem_id, store.kem_sig, store.kem_one_time, store.previous_signed_prekey,
            store.previous_kem, store.next_id, store.last_resort_seen, store.legacy_last_resort_blocked, found)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.take_one_time_kem_loop_frame

/--
info: Tacenta.UnitLifecycleEstablishResponder.take_one_time_kem_frame : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (id : Aeneas.Std.U32) (x : Option tacenta_session_unit.tacenta_boundary.kem.KeyPair)
  (store' : tacenta_session_unit.lifecycle.PrekeyStore),
  store.take_one_time_kem id = Aeneas.Std.Result.ok (x, store') →
    store' =
      { identity_public := store.identity_public, signed_prekey_secret := store.signed_prekey_secret,
        signed_prekey_id := store.signed_prekey_id, signed_prekey_sig := store.signed_prekey_sig,
        one_time := store.one_time, kem := store.kem, kem_id := store.kem_id, kem_sig := store.kem_sig,
        kem_one_time := store'.kem_one_time, previous_signed_prekey := store.previous_signed_prekey,
        previous_kem := store.previous_kem, next_id := store.next_id, last_resort_seen := store.last_resort_seen,
        legacy_last_resort_blocked := store.legacy_last_resort_blocked }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.take_one_time_kem_frame

/--
info: @Tacenta.UnitLifecycleEstablishResponder.take_one_time_loop_frame : ∀ [inst : Tacenta.SessionUnitT1.DerivedKeysModel]
  (store : tacenta_session_unit.lifecycle.PrekeyStore) (id : Aeneas.Std.U32) (index : Aeneas.Std.Usize),
  ↑index ≤ (↑(Tacenta.SessionUnitT1.DerivedKeysModel.contents store.one_time)).length →
    Aeneas.Std.WP.spec (store.take_one_time_loop id index) fun r =>
      ∃ found,
        r =
          (store.identity_public, store.signed_prekey_secret, store.signed_prekey_id, store.signed_prekey_sig,
            store.one_time, store.kem, store.kem_id, store.kem_sig, store.kem_one_time, store.previous_signed_prekey,
            store.previous_kem, store.next_id, store.last_resort_seen, store.legacy_last_resort_blocked, found)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.take_one_time_loop_frame

/--
info: @Tacenta.UnitLifecycleEstablishResponder.take_one_time_frame : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  (store : tacenta_session_unit.lifecycle.PrekeyStore) (id : Aeneas.Std.U32) (b : Bool)
  (store' : tacenta_session_unit.lifecycle.PrekeyStore),
  store.take_one_time id = Aeneas.Std.Result.ok (b, store') →
    store' =
      { identity_public := store.identity_public, signed_prekey_secret := store.signed_prekey_secret,
        signed_prekey_id := store.signed_prekey_id, signed_prekey_sig := store.signed_prekey_sig,
        one_time := store'.one_time, kem := store.kem, kem_id := store.kem_id, kem_sig := store.kem_sig,
        kem_one_time := store.kem_one_time, previous_signed_prekey := store.previous_signed_prekey,
        previous_kem := store.previous_kem, next_id := store.next_id, last_resort_seen := store.last_resort_seen,
        legacy_last_resort_blocked := store.legacy_last_resort_blocked }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.take_one_time_frame

/--
info: @Tacenta.UnitLifecycleEstablishResponder.vec_push_ok : ∀ {α : Type} {v v' : Aeneas.Std.alloc.vec.Vec α} {x : α},
  v.push x = Aeneas.Std.Result.ok v' → ↑v' = ↑v ++ [x]
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.vec_push_ok

/--
info: @Tacenta.UnitLifecycleEstablishResponder.responderCommit_effects : ∀ [Tacenta.SessionUnitT1.DerivedKeysModel]
  {store store' : tacenta_session_unit.lifecycle.PrekeyStore} {kemId oneTimeId : Aeneas.Std.U32} {lastResort : Bool}
  {replay : Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize)},
  Tacenta.UnitLifecycleEstablishResponder.ResponderCommit store kemId oneTimeId lastResort replay store' →
    store' =
        { identity_public := store.identity_public, signed_prekey_secret := store.signed_prekey_secret,
          signed_prekey_id := store.signed_prekey_id, signed_prekey_sig := store.signed_prekey_sig,
          one_time := store'.one_time, kem := store.kem, kem_id := store.kem_id, kem_sig := store.kem_sig,
          kem_one_time := store'.kem_one_time, previous_signed_prekey := store.previous_signed_prekey,
          previous_kem := store.previous_kem, next_id := store.next_id, last_resort_seen := store'.last_resort_seen,
          legacy_last_resort_blocked := store.legacy_last_resort_blocked } ∧
      (lastResort = true → store'.kem_one_time = store.kem_one_time) ∧
        (oneTimeId = tacenta_session_unit.serialization.ABSENT_ID → store'.one_time = store.one_time) ∧
          (replay = none → store'.last_resort_seen = store.last_resort_seen) ∧
            ∀ (fp : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
              replay = some fp → ↑store'.last_resort_seen = (↑store.last_resort_seen).concat (kemId, fp)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responderCommit_effects

/--
info: Tacenta.UnitLifecycleEstablishResponder.replay_ok : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (kemId : Aeneas.Std.U32) (sk : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (lastResort : Bool)
  (r : Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize)),
  tacenta_session_unit.lifecycle.responder_replay_fingerprint store kemId sk lastResort =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok r) →
    (lastResort = false → r = none) ∧
      (lastResort = true →
        ∃ fp, r = some fp ∧ tacenta_session_unit.lifecycle.last_resort_fingerprint sk = Aeneas.Std.Result.ok fp)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.replay_ok

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_cases : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (msg : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R)
  (out :
    Aeneas.Std.core.result.Result (tacenta_session_unit.lifecycle.Session × Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
        tacenta_session_unit.lifecycle.Error ×
      tacenta_session_unit.lifecycle.PrekeyStore × R),
  tacenta_session_unit.lifecycle.establish_responder rc crc our store msg rng = Aeneas.Std.Result.ok out →
    (∃ e,
        Tacenta.UnitLifecycleEstablishResponder.PrepareRefusal e ∧
          out = (Aeneas.Std.core.result.Result.Err e, store, rng)) ∨
      ∃ p inner,
        tacenta_session_unit.lifecycle.Session.decrypt_ratchet rc crc p.session p.message rng =
            Aeneas.Std.Result.ok inner ∧
          ((∃ e,
              inner.1 = Aeneas.Std.core.result.Result.Err e ∧
                out = (Aeneas.Std.core.result.Result.Err e, store, inner.2.2)) ∨
            ∃ pt store',
              inner.1 = Aeneas.Std.core.result.Result.Ok pt ∧
                Tacenta.UnitLifecycleEstablishResponder.ResponderCommit store p.decoded.kem_prekey_id
                    p.decoded.one_time_prekey_id p.lastResort p.replay store' ∧
                  out = (Aeneas.Std.core.result.Result.Ok (inner.2.1, pt), store', inner.2.2))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_cases

/--
info: @Tacenta.UnitLifecycleEstablishResponder.random32_draws : ∀ {o o' : Model.Lifecycle.Oracle} {c : Model.Lifecycle.Key},
  Model.Lifecycle.random32 o = some (c, o') → o.draws = c :: o'.draws
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.random32_draws

/--
info: @Tacenta.UnitLifecycleEstablishResponder.responder_prepared_decrypt_refines : ∀
  {our : tacenta_session_unit.lifecycle.Identity} {store : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8} {R : Type} (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
  (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
  (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
              Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                  @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                Tacenta.SessionUnitDecoderBound.DivCeilValue →
                  ∀ (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg) (rng : R),
                    trace rng = oracle.draws →
                      Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace p.session
                          (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) p.message rng →
                        ∃ inner,
                          tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng p.session p.message
                                rng =
                              Aeneas.Std.Result.ok inner ∧
                            Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem inner
                              (Model.Lifecycle.decryptRatchet view oracle
                                (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p)
                                (Tacenta.UnitLifecycleT3.sliceOf p.message))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responder_prepared_decrypt_refines

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_refines : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
              Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                  @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                Tacenta.SessionUnitDecoderBound.DivCeilValue →
                  ∀ (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
                    (msg : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R)
                    (out :
                      Aeneas.Std.core.result.Result
                          (tacenta_session_unit.lifecycle.Session × Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
                          tacenta_session_unit.lifecycle.Error ×
                        tacenta_session_unit.lifecycle.PrekeyStore × R),
                    tacenta_session_unit.lifecycle.establish_responder rngCore cryptoRng our store msg rng =
                        Aeneas.Std.Result.ok out →
                      trace rng = oracle.draws →
                        (∀ (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
                            Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace p.session
                              (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) p.message rng) →
                          (∃ e,
                              Tacenta.UnitLifecycleEstablishResponder.PrepareRefusal e ∧
                                out = (Aeneas.Std.core.result.Result.Err e, store, rng)) ∨
                            ∃ p inner,
                              tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng p.session
                                    p.message rng =
                                  Aeneas.Std.Result.ok inner ∧
                                Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem inner
                                    (Model.Lifecycle.decryptRatchet view oracle
                                      (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p)
                                      (Tacenta.UnitLifecycleT3.sliceOf p.message)) ∧
                                  ((∃ e,
                                      inner.1 = Aeneas.Std.core.result.Result.Err e ∧
                                        out = (Aeneas.Std.core.result.Result.Err e, store, inner.2.2) ∧
                                          (trace inner.2.2 = trace rng ∨ ∃ d, trace rng = d :: trace inner.2.2)) ∨
                                    ∃ pt store',
                                      inner.1 = Aeneas.Std.core.result.Result.Ok pt ∧
                                        Tacenta.UnitLifecycleEstablishResponder.ResponderCommit store
                                            p.decoded.kem_prekey_id p.decoded.one_time_prekey_id p.lastResort p.replay
                                            store' ∧
                                          out = (Aeneas.Std.core.result.Result.Ok (inner.2.1, pt), store', inner.2.2) ∧
                                            ∃ d, trace rng = d :: trace inner.2.2)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_refines

/--
info: Tacenta.UnitLifecycleEstablishResponder.readBe32_be32 : ∀ (n : UInt32) (rest : List UInt8),
  Model.Messages.readBe32 (Model.Messages.be32 n ++ rest) = some (n, rest)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.readBe32_be32

/--
info: Tacenta.UnitLifecycleEstablishResponder.takeSplit_append : ∀ (a b : List UInt8),
  Model.Messages.take? a.length (a ++ b) = some (a, b)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.takeSplit_append

/--
info: Tacenta.UnitLifecycleEstablishResponder.decodeInitial_encodeInitial : ∀ (i e ct : List UInt8) (s o k : UInt32)
  (m : List UInt8),
  i.length = 33 →
    e.length = 33 →
      Model.Messages.checkCurve i = some () →
        Model.Messages.checkCurve e = some () →
          Model.Messages.checkKey (List.drop 1 i) = some () →
            Model.Messages.checkKey (List.drop 1 e) = some () →
              ct.length < 2 ^ 32 →
                Model.Messages.decodeInitial (Model.Messages.encodeInitial i e ct s o k m) =
                  some
                    { identity := i, ephemeral := e, kemCiphertext := ct, signedPrekeyId := s, oneTimeId := o,
                      kemPrekeyId := k, ratchetMessage := m }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.decodeInitial_encodeInitial

/--
info: Tacenta.UnitLifecycleEstablishResponder.wireKey_length : Tacenta.UnitLifecycleEstablishResponder.wireKey.length = 33
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.wireKey_length

/--
info: Tacenta.UnitLifecycleEstablishResponder.wireKey_curve : Model.Messages.checkCurve
    Tacenta.UnitLifecycleEstablishResponder.wireKey =
  some ()
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.wireKey_curve

/--
info: Tacenta.UnitLifecycleEstablishResponder.wireKey_key : Model.Messages.checkKey
    (List.drop 1 Tacenta.UnitLifecycleEstablishResponder.wireKey) =
  some ()
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.wireKey_key

/--
info: Tacenta.UnitLifecycleEstablishResponder.ephKey_length : ∀ (b : Bool),
  (Tacenta.UnitLifecycleEstablishResponder.ephKey b).length = 33
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.ephKey_length

/--
info: Tacenta.UnitLifecycleEstablishResponder.ephKey_curve : ∀ (b : Bool),
  Model.Messages.checkCurve (Tacenta.UnitLifecycleEstablishResponder.ephKey b) = some ()
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.ephKey_curve

/--
info: Tacenta.UnitLifecycleEstablishResponder.ephKey_key : ∀ (b : Bool),
  Model.Messages.checkKey (List.drop 1 (Tacenta.UnitLifecycleEstablishResponder.ephKey b)) = some ()
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.ephKey_key

/--
info: Tacenta.UnitLifecycleEstablishResponder.successBytes_length : ∀ (zeroEph : Bool)
  (ct frame : Aeneas.Std.Slice Aeneas.Std.U8),
  (Tacenta.UnitLifecycleEstablishResponder.successBytes zeroEph ct frame).length = 84 + (↑ct).length + (↑frame).length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.successBytes_length

/--
info: Tacenta.UnitLifecycleEstablishResponder.successBytes_le : ∀ (zeroEph : Bool)
  (ct frame : Aeneas.Std.Slice Aeneas.Std.U8),
  (↑ct).length ≤ 4096 →
    (↑frame).length ≤ 4096 →
      (Tacenta.UnitLifecycleEstablishResponder.successBytes zeroEph ct frame).length ≤ Aeneas.Std.Usize.max
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.successBytes_le

/--
info: Tacenta.UnitLifecycleEstablishResponder.decode_successMessage : ∀ (zeroEph : Bool)
  (ct frame : Aeneas.Std.Slice Aeneas.Std.U8) (hct : (↑ct).length ≤ 4096) (hframe : (↑frame).length ≤ 4096),
  ∃ d,
    tacenta_session_unit.tacenta_wire.decode_initial
          (Tacenta.UnitLifecycleEstablishResponder.successMessage zeroEph ct frame hct hframe) =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) ∧
      Tacenta.SessionUnitWireInitialT3.initialOf d =
        { identity := Tacenta.UnitLifecycleEstablishResponder.wireKey,
          ephemeral := Tacenta.UnitLifecycleEstablishResponder.ephKey zeroEph,
          kemCiphertext := Tacenta.UnitLifecycleT3.sliceOf ct, signedPrekeyId := 0, oneTimeId := 0, kemPrekeyId := 0,
          ratchetMessage := Tacenta.UnitLifecycleT3.sliceOf frame }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.decode_successMessage

/--
info: Tacenta.UnitLifecycleEstablishResponder.replay_fresh : Tacenta.SessionUnitT1.HmacTotal →
  ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore),
    ↑store.last_resort_seen = [] →
      ∀ (kemId : Aeneas.Std.U32) (sk : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
        ∃ fp,
          tacenta_session_unit.lifecycle.last_resort_fingerprint sk = Aeneas.Std.Result.ok fp ∧
            tacenta_session_unit.lifecycle.responder_replay_fingerprint store kemId sk true =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (some fp))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.replay_fresh

/--
info: @Tacenta.UnitLifecycleEstablishResponder.map_u8_inj : ∀ {l1 l2 : List Aeneas.Std.U8},
  List.map Tacenta.SessionUnitBraidT3.u8 l1 = List.map Tacenta.SessionUnitBraidT3.u8 l2 → l1 = l2
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.map_u8_inj

/--
info: @Tacenta.UnitLifecycleEstablishResponder.u32_of_ofNat : ∀ {x : Aeneas.Std.U32} {n : ℕ},
  n < 2 ^ 32 → UInt32.ofNat ↑x = UInt32.ofNat n → ↑x = n
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.u32_of_ofNat

/--
info: Tacenta.UnitLifecycleEstablishResponder.basePoint_length : (9#u8 :: List.replicate 31 0#u8).length = ↑32#usize
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.basePoint_length

/--
info: Tacenta.UnitLifecycleEstablishResponder.arrayOf_basePoint : Tacenta.UnitLifecycleT3.arrayOf
    Tacenta.UnitLifecycleEstablishResponder.basePoint =
  Tacenta.UnitLifecycleEstablishResponder.basePointBytes
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.arrayOf_basePoint

/--
info: Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical : Tacenta.SessionUnitT1.canonicalX25519
    Tacenta.UnitLifecycleEstablishResponder.basePoint =
  true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.basePoint_canonical

/--
info: Tacenta.UnitLifecycleEstablishResponder.successMessage_decoded : ∀ (zeroEph : Bool)
  (ct frame : Aeneas.Std.Slice Aeneas.Std.U8) (hct : (↑ct).length ≤ 4096) (hframe : (↑frame).length ≤ 4096),
  ∃ d,
    tacenta_session_unit.tacenta_wire.decode_initial
          (Tacenta.UnitLifecycleEstablishResponder.successMessage zeroEph ct frame hct hframe) =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok d) ∧
      d.signed_prekey_id = 0#u32 ∧
        d.one_time_prekey_id = 0#u32 ∧
          d.kem_prekey_id = 0#u32 ∧
            Tacenta.UnitLifecycleT3.sliceOf d.identity.deref = Tacenta.UnitLifecycleEstablishResponder.wireKey ∧
              Tacenta.UnitLifecycleT3.sliceOf d.ephemeral.deref =
                  Tacenta.UnitLifecycleEstablishResponder.ephKey zeroEph ∧
                d.kem_ciphertext.deref = ct ∧ d.message.deref = frame
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.successMessage_decoded

/--
info: Tacenta.UnitLifecycleEstablishResponder.decode_ec_wireKey : ∀ (s : Aeneas.Std.Slice Aeneas.Std.U8),
  Tacenta.UnitLifecycleT3.sliceOf s = Tacenta.UnitLifecycleEstablishResponder.wireKey →
    ∀ (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
      tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes
            Tacenta.UnitLifecycleEstablishResponder.basePoint =
          Aeneas.Std.Result.ok pkb →
        tacenta_session_unit.decode_ec s = Aeneas.Std.Result.ok (some pkb)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.decode_ec_wireKey

/--
info: Tacenta.UnitLifecycleEstablishResponder.responder_shared_secret_ok : Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
  Tacenta.SessionUnitSessionT1.HkdfTotal →
    ∀ [Tacenta.SessionUnitSessionT1.ZeroizingModel] (pkb : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
      tacenta_session_unit.is_valid_identity_key pkb = Aeneas.Std.Result.ok true →
        (∀ (k : tacenta_session_unit.tacenta_boundary.dh.PrivateKey),
            ∃ x, k.agree pkb = Aeneas.Std.Result.ok (some x)) →
          ∀ (ik sp : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
            (enc : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
            ∃ sec,
              tacenta_session_unit.responder_shared_secret ik sp none pkb pkb enc =
                Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok sec)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responder_shared_secret_ok

/--
info: @Tacenta.UnitLifecycleEstablishResponder.responder_prepared_inhabited : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rc),
  Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
    ∀ (our : tacenta_session_unit.lifecycle.Identity) (frame : Aeneas.Std.Slice Aeneas.Std.U8),
      (↑frame).length ≤ 4096 → ∃ store msg p, p.message = frame ∧ ↑store.last_resort_seen = [] ∧ p.lastResort = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responder_prepared_inhabited

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_returns : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rngCore) [Tacenta.SessionUnitT1.DerivedKeysModel]
  (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (msg : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  Tacenta.UnitLifecycleT1.EstablishResponderHeadroom store →
    ∃ out,
      tacenta_session_unit.lifecycle.establish_responder rngCore cryptoRng our store msg rng = Aeneas.Std.Result.ok out
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_returns

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_short_message_refused : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (msg : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
  (↑msg).length < 2 →
    tacenta_session_unit.lifecycle.establish_responder rngCore cryptoRng our store msg rng =
      Aeneas.Std.Result.ok
        (Aeneas.Std.core.result.Result.Err
            (tacenta_session_unit.lifecycle.Error.Decode tacenta_session_unit.tacenta_wire.DecodeError.TooShort),
          store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_short_message_refused

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_at_parts : ∀
  {our : tacenta_session_unit.lifecycle.Identity} {store : tacenta_session_unit.lifecycle.PrekeyStore}
  {msg : Aeneas.Std.Slice Aeneas.Std.U8} {R : Type} (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
  (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg) (rng : R),
  tacenta_session_unit.lifecycle.establish_responder rngCore cryptoRng our store msg rng = do
    let (r, session, rng1) ←
      tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng p.session p.message rng
    match r with
      | Aeneas.Std.core.result.Result.Err e => Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, store, rng1)
      | Aeneas.Std.core.result.Result.Ok pt => do
        let store1 ←
          if p.lastResort = true then Aeneas.Std.Result.ok store
            else do
              let (_, s) ← store.take_one_time_kem p.decoded.kem_prekey_id
              Aeneas.Std.Result.ok s
        let store2 ←
          if (p.decoded.one_time_prekey_id != tacenta_session_unit.serialization.ABSENT_ID) = true then do
              let (_, s) ← store1.take_one_time p.decoded.one_time_prekey_id
              Aeneas.Std.Result.ok s
            else Aeneas.Std.Result.ok store1
        match p.replay with
          | none => Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (session, pt), store2, rng1)
          | some fp => do
            let i ← store2.last_resort_seen_for p.decoded.kem_prekey_id
            Aeneas.Std.massert (i < tacenta_session_unit.lifecycle.MAX_LAST_RESORT_SEEN)
            let v ← store2.last_resort_seen.push (p.decoded.kem_prekey_id, fp)
            Aeneas.Std.Result.ok
                (Aeneas.Std.core.result.Result.Ok (session, pt),
                  { identity_public := store2.identity_public, signed_prekey_secret := store2.signed_prekey_secret,
                    signed_prekey_id := store2.signed_prekey_id, signed_prekey_sig := store2.signed_prekey_sig,
                    one_time := store2.one_time, kem := store2.kem, kem_id := store2.kem_id, kem_sig := store2.kem_sig,
                    kem_one_time := store2.kem_one_time, previous_signed_prekey := store2.previous_signed_prekey,
                    previous_kem := store2.previous_kem, next_id := store2.next_id, last_resort_seen := v,
                    legacy_last_resort_blocked := store2.legacy_last_resort_blocked },
                  rng1)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_at_parts

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_unknown_prekey_refused : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore) (rng : R)
  (ct frame : Aeneas.Std.Slice Aeneas.Std.U8) (hct : (↑ct).length ≤ 4096) (hframe : (↑frame).length ≤ 4096),
  store.signed_prekey_id ≠ 0#u32 →
    store.previous_signed_prekey = none →
      tacenta_session_unit.lifecycle.establish_responder rngCore cryptoRng our store
          (Tacenta.UnitLifecycleEstablishResponder.successMessage false ct frame hct hframe) rng =
        Aeneas.Std.Result.ok
          (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.UnknownPrekeyId, store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_unknown_prekey_refused

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_legacy_refused : ∀ {R : Type},
  Tacenta.SessionUnitBraidT1.ZeroizingArrayRoundTrip →
    ∀ (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
      (our : tacenta_session_unit.lifecycle.Identity) (store : tacenta_session_unit.lifecycle.PrekeyStore) (rng : R)
      (ct frame : Aeneas.Std.Slice Aeneas.Std.U8) (hct : (↑ct).length ≤ 4096) (hframe : (↑frame).length ≤ 4096),
      store.signed_prekey_id = 0#u32 →
        store.kem_id = 0#u32 →
          0#u32 ∈ ↑store.legacy_last_resort_blocked →
            tacenta_session_unit.lifecycle.establish_responder rngCore cryptoRng our store
                (Tacenta.UnitLifecycleEstablishResponder.successMessage false ct frame hct hframe) rng =
              Aeneas.Std.Result.ok
                (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.LegacyLastResortRecord, store,
                  rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_legacy_refused

/--
info: Tacenta.UnitLifecycleEstablishResponder.array_eq_decide : ∀ (a b : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Aeneas.Std.core.array.equality.PartialEqArray.eq Aeneas.Std.core.cmp.PartialEqU8 a b =
    Aeneas.Std.Result.ok (decide (a = b))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.array_eq_decide

/--
info: Tacenta.UnitLifecycleEstablishResponder.replay_loop_absent : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (fp : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  (∀ e ∈ ↑store.last_resort_seen, e.2 ≠ fp) →
    Aeneas.Std.WP.spec (tacenta_session_unit.lifecycle.responder_replay_fingerprint_loop store fp false 0#usize)
      fun r =>
      r =
        (store.identity_public, store.signed_prekey_secret, store.signed_prekey_id, store.signed_prekey_sig,
          store.one_time, store.kem, store.kem_id, store.kem_sig, store.kem_one_time, store.previous_signed_prekey,
          store.previous_kem, store.next_id, store.last_resort_seen, store.legacy_last_resort_blocked, false)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.replay_loop_absent

/--
info: Tacenta.UnitLifecycleEstablishResponder.seen_for_loop_all : ∀ (store : tacenta_session_unit.lifecycle.PrekeyStore)
  (k : Aeneas.Std.U32),
  (∀ e ∈ ↑store.last_resort_seen, e.1 = k) →
    Aeneas.Std.WP.spec (store.last_resort_seen_for_loop k 0#usize 0#usize) fun r =>
      ↑r = (↑store.last_resort_seen).length
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.seen_for_loop_all

/--
info: Tacenta.UnitLifecycleEstablishResponder.array_eq_self : ∀ (a : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Aeneas.Std.core.array.equality.PartialEqArray.eq Aeneas.Std.core.cmp.PartialEqU8 a a = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.array_eq_self

/--
info: Tacenta.UnitLifecycleEstablishResponder.decode_ec_zeroWire : ∀ (s : Aeneas.Std.Slice Aeneas.Std.U8),
  Tacenta.UnitLifecycleT3.sliceOf s = Tacenta.UnitLifecycleEstablishResponder.zeroWire →
    ∀ (z : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes),
      tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes Tacenta.UnitSatisfiabilityBraidStates.zeros32 =
          Aeneas.Std.Result.ok z →
        tacenta_session_unit.decode_ec s = Aeneas.Std.Result.ok (some z)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.decode_ec_zeroWire

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_noncontributory_refused : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rc),
  Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
    Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
      ∀ (our : tacenta_session_unit.lifecycle.Identity) (rng : R) (frame : Aeneas.Std.Slice Aeneas.Std.U8),
        (↑frame).length ≤ 4096 →
          ∃ store msg,
            tacenta_session_unit.lifecycle.establish_responder rc crc our store msg rng =
              Aeneas.Std.Result.ok
                (Aeneas.Std.core.result.Result.Err
                    (tacenta_session_unit.lifecycle.Error.Handshake
                      tacenta_session_unit.SessionError.NonContributoryAgreement),
                  store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_noncontributory_refused

/--
info: @Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.refines : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView}
  {oracle : Model.Lifecycle.Oracle} {our : tacenta_session_unit.lifecycle.Identity}
  {store : tacenta_session_unit.lifecycle.PrekeyStore} {msg : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R},
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses rngCore cryptoRng trace dh view oracle our store msg
      rng →
    ∃ out,
      tacenta_session_unit.lifecycle.establish_responder rngCore cryptoRng our store msg rng =
          Aeneas.Std.Result.ok out ∧
        ((∃ e,
            Tacenta.UnitLifecycleEstablishResponder.PrepareRefusal e ∧
              out = (Aeneas.Std.core.result.Result.Err e, store, rng)) ∨
          ∃ p inner,
            tacenta_session_unit.lifecycle.Session.decrypt_ratchet rngCore cryptoRng p.session p.message rng =
                Aeneas.Std.Result.ok inner ∧
              Tacenta.UnitLifecycleT3.StepRefines trace dh oracle.braidKem inner
                  (Model.Lifecycle.decryptRatchet view oracle
                    (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p)
                    (Tacenta.UnitLifecycleT3.sliceOf p.message)) ∧
                ((∃ e,
                    inner.1 = Aeneas.Std.core.result.Result.Err e ∧
                      out = (Aeneas.Std.core.result.Result.Err e, store, inner.2.2) ∧
                        (trace inner.2.2 = trace rng ∨ ∃ d, trace rng = d :: trace inner.2.2)) ∨
                  ∃ pt store',
                    inner.1 = Aeneas.Std.core.result.Result.Ok pt ∧
                      Tacenta.UnitLifecycleEstablishResponder.ResponderCommit store p.decoded.kem_prekey_id
                          p.decoded.one_time_prekey_id p.lastResort p.replay store' ∧
                        out = (Aeneas.Std.core.result.Result.Ok (inner.2.1, pt), store', inner.2.2) ∧
                          ∃ d, trace rng = d :: trace inner.2.2))
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.refines

/--
info: Tacenta.UnitLifecycleEstablishResponder.sampleMessage_le : (↑Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage).length ≤
  4096
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.sampleMessage_le

/--
info: Tacenta.UnitLifecycleEstablishResponder.responder_route_hypotheses_jointly_satisfiable : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
          ∀ (our : tacenta_session_unit.lifecycle.Identity),
            ∃ oracle store msg,
              oracle.braidKem = K ∧
                (∀ (q : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
                    q.message = Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage) ∧
                  ∀ (view : Model.Lifecycle.CodewordView),
                    Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses
                      Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                      Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle our store msg
                      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responder_route_hypotheses_jointly_satisfiable

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_replay_refused : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rc),
  Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
    ∀ (our : tacenta_session_unit.lifecycle.Identity) (rng : R),
      ∃ store msg,
        (↑store.last_resort_seen).length = 1 ∧
          tacenta_session_unit.lifecycle.establish_responder rc crc our store msg rng =
            Aeneas.Std.Result.ok
              (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.ReplayedLastResort, store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_replay_refused

/--
info: Tacenta.UnitLifecycleEstablishResponder.full_record_length_le : ∀
  (e : Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 32#usize), (List.replicate 1024 e).length ≤ 4294967295
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.full_record_length_le

/--
info: Tacenta.UnitLifecycleEstablishResponder.otherThan_ne : ∀ (fp : Aeneas.Std.Array Aeneas.Std.U8 32#usize),
  Tacenta.UnitLifecycleEstablishResponder.otherThan fp ≠ fp
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.otherThan_ne

/--
info: @Tacenta.UnitLifecycleEstablishResponder.establish_responder_record_full_refused : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R)
  (contracts : Tacenta.UnitLifecycleT1.EstablishResponderContracts rc),
  Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
    ∀ (our : tacenta_session_unit.lifecycle.Identity) (rng : R),
      ∃ store msg,
        (↑store.last_resort_seen).length = 1024 ∧
          tacenta_session_unit.lifecycle.establish_responder rc crc our store msg rng =
            Aeneas.Std.Result.ok
              (Aeneas.Std.core.result.Result.Err tacenta_session_unit.lifecycle.Error.LastResortRecordFull, store, rng)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.establish_responder_record_full_refused

/--
info: Tacenta.UnitLifecycleEstablishResponder.responder_route_inner_refusal_reachable : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
      Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
        Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape Tacenta.UnitSatisfiabilityJoint.Interp.real →
          Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
            ∀ (our : tacenta_session_unit.lifecycle.Identity) (view : Model.Lifecycle.CodewordView),
              ∃ oracle store msg e rng',
                oracle.braidKem = K ∧
                  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses
                      Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                      Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle our store msg
                      Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng ∧
                    tacenta_session_unit.lifecycle.establish_responder Tacenta.UnitLifecycleIntegrationScreen.byteRng
                          Tacenta.UnitLifecycleIntegrationScreen.byteCrc our store msg
                          Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err e, store, rng') ∧
                      Tacenta.UnitLifecycleT3.refusalOf e =
                        Model.Lifecycle.Refusal.handshake Model.Lifecycle.HandshakeRefusal.nonContributoryAgreement
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responder_route_inner_refusal_reachable

/--
info: Tacenta.UnitLifecycleEstablishResponder.responder_route_laws_model : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
    Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished
    Tacenta.UnitLifecycleEstablishedDecrypt.viewEstablished Model.Braid.toyKem
    @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
  Nonempty
      (Tacenta.UnitSatisfiabilityJoint.ResponderAxiom Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished
        Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
    Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape
        Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
          Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
        Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape
          Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleEstablishResponder.responder_route_laws_model

/--
info: @[reducible] def Tacenta.UnitLifecycleEstablishResponder.z32 : tacenta_session_unit.zeroize.Zeroize
  (Aeneas.Std.Array Aeneas.Std.U8 32#usize) :=
tacenta_session_unit.Array.Insts.ZeroizeZeroize 32#usize
  (tacenta_session_unit.zeroize.Zeroize.Blanket tacenta_session_unit.U8.Insts.ZeroizeDefaultIsZeroes)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.z32

/--
info: @[reducible] def Tacenta.UnitLifecycleEstablishResponder.fullSlice : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) :=
fun a =>
  Aeneas.Std.core.array.Array.index
    (Aeneas.Std.core.ops.index.IndexSlice
      (tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice Aeneas.Std.U8))
    a ()
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.fullSlice

/--
info: structure Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts (our : tacenta_session_unit.lifecycle.Identity)
  (store : tacenta_session_unit.lifecycle.PrekeyStore) (msg : Aeneas.Std.Slice Aeneas.Std.U8) : Type
number of parameters: 3
fields:
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.decoded : tacenta_session_unit.tacenta_wire.DecodedInitial
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.signedSecret : tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.kemSlot : tacenta_session_unit.lifecycle.KemKeySlot
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.lastResort : Bool
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.peerIdentity : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.peerEphemeral : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.oneTime : Option
      tacenta_session_unit.tacenta_boundary.dh.PrivateKey
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.kemSecret : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.kemSecretZ : tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.signedBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.signedPrekey : tacenta_session_unit.tacenta_boundary.dh.PrivateKey
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.shared : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.secretZ : tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.secret : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.replay : Option
      (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.tripleSecret : Aeneas.Std.Slice Aeneas.Std.U8
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ratchetPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ratchetBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.triple : tacenta_session_unit.tacenta_triple.State
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.braidSecret : Aeneas.Std.Slice Aeneas.Std.U8
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.braid : tacenta_session_unit.tacenta_braid.Braid
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ratchetPrivate : tacenta_session_unit.tacenta_boundary.dh.PrivateKey
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ourPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.identityAd : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.ephemeralCopy : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hDecode : tacenta_session_unit.tacenta_wire.decode_initial
        msg =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok self.decoded)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hSigned : tacenta_session_unit.lifecycle.responder_signed_prekey_secret
        store self.decoded.signed_prekey_id =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok self.signedSecret)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hSlot : tacenta_session_unit.lifecycle.responder_kem_slot
        store self.decoded.kem_prekey_id =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (self.kemSlot, self.lastResort))
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hCurve : tacenta_session_unit.lifecycle.responder_curve_inputs
        self.decoded.identity.deref self.decoded.ephemeral.deref =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (self.peerIdentity, self.peerEphemeral))
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hOneTime : tacenta_session_unit.lifecycle.responder_one_time_key
        store self.decoded.one_time_prekey_id =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok self.oneTime)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hDecaps : tacenta_session_unit.lifecycle.responder_decapsulate
        store self.kemSlot self.decoded.kem_ciphertext.deref =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok self.kemSecret)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hKemSecretZ : tacenta_session_unit.zeroize.Zeroizing.new
        Tacenta.UnitLifecycleEstablishResponder.z32 self.kemSecret =
      Aeneas.Std.Result.ok self.kemSecretZ
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hSignedBytes : tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        Tacenta.UnitLifecycleEstablishResponder.z32 self.signedSecret =
      Aeneas.Std.Result.ok self.signedBytes
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hSignedPrekey : tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes
        self.signedBytes =
      Aeneas.Std.Result.ok self.signedPrekey
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hShared : ∃ identityKey encapsulated,
      our.dh_key = Aeneas.Std.Result.ok identityKey ∧
        tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleEstablishResponder.z32
              self.kemSecretZ =
            Aeneas.Std.Result.ok encapsulated ∧
          tacenta_session_unit.responder_shared_secret identityKey self.signedPrekey self.oneTime self.peerIdentity
              self.peerEphemeral encapsulated =
            Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok self.shared)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hSecretZ : tacenta_session_unit.zeroize.Zeroizing.new
        Tacenta.UnitLifecycleEstablishResponder.z32 self.shared =
      Aeneas.Std.Result.ok self.secretZ
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hSecret : tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        Tacenta.UnitLifecycleEstablishResponder.z32 self.secretZ =
      Aeneas.Std.Result.ok self.secret
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hReplay : tacenta_session_unit.lifecycle.responder_replay_fingerprint
        store self.decoded.kem_prekey_id self.secret self.lastResort =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok self.replay)
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hTripleSecret : Tacenta.UnitLifecycleEstablishResponder.fullSlice
        self.secret =
      Aeneas.Std.Result.ok self.tripleSecret
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hRatchetPublic : self.signedPrekey.public_key =
      Aeneas.Std.Result.ok self.ratchetPublic
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hRatchetBytes : self.ratchetPublic.as_bytes =
      Aeneas.Std.Result.ok self.ratchetBytes
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hTriple : tacenta_session_unit.tacenta_triple.State.init_receiver
        self.tripleSecret self.ratchetBytes tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
      Aeneas.Std.Result.ok self.triple
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hBraidSecret : Tacenta.UnitLifecycleEstablishResponder.fullSlice
        self.secret =
      Aeneas.Std.Result.ok self.braidSecret
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hBraid : tacenta_session_unit.tacenta_braid.Braid.responder
        self.braidSecret =
      Aeneas.Std.Result.ok self.braid
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hRatchetPrivate : tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes
        self.signedBytes =
      Aeneas.Std.Result.ok self.ratchetPrivate
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hOurPublic : our.public =
      Aeneas.Std.Result.ok self.ourPublic
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hIdentityAd : tacenta_session_unit.lifecycle.identity_ad
        self.peerIdentity self.ourPublic =
      Aeneas.Std.Result.ok self.identityAd
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.hEphemeralCopy : Aeneas.Std.alloc.vec.CloneVec.clone
        Aeneas.Std.core.clone.CloneU8 self.decoded.ephemeral =
      Aeneas.Std.Result.ok self.ephemeralCopy
constructor:
  Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.mk {our : tacenta_session_unit.lifecycle.Identity}
    {store : tacenta_session_unit.lifecycle.PrekeyStore} {msg : Aeneas.Std.Slice Aeneas.Std.U8}
    (decoded : tacenta_session_unit.tacenta_wire.DecodedInitial)
    (signedSecret : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (kemSlot : tacenta_session_unit.lifecycle.KemKeySlot) (lastResort : Bool)
    (peerIdentity peerEphemeral : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
    (oneTime : Option tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (kemSecret : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (kemSecretZ : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (signedBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (signedPrekey : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (shared : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
    (secretZ : tacenta_session_unit.zeroize.Zeroizing (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (secret : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (replay : Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (tripleSecret : Aeneas.Std.Slice Aeneas.Std.U8)
    (ratchetPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
    (ratchetBytes : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (triple : tacenta_session_unit.tacenta_triple.State)
    (braidSecret : Aeneas.Std.Slice Aeneas.Std.U8) (braid : tacenta_session_unit.tacenta_braid.Braid)
    (ratchetPrivate : tacenta_session_unit.tacenta_boundary.dh.PrivateKey)
    (ourPublic : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes)
    (identityAd ephemeralCopy : Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8)
    (hDecode :
      tacenta_session_unit.tacenta_wire.decode_initial msg =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok decoded))
    (hSigned :
      tacenta_session_unit.lifecycle.responder_signed_prekey_secret store decoded.signed_prekey_id =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok signedSecret))
    (hSlot :
      tacenta_session_unit.lifecycle.responder_kem_slot store decoded.kem_prekey_id =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (kemSlot, lastResort)))
    (hCurve :
      tacenta_session_unit.lifecycle.responder_curve_inputs decoded.identity.deref decoded.ephemeral.deref =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (peerIdentity, peerEphemeral)))
    (hOneTime :
      tacenta_session_unit.lifecycle.responder_one_time_key store decoded.one_time_prekey_id =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok oneTime))
    (hDecaps :
      tacenta_session_unit.lifecycle.responder_decapsulate store kemSlot decoded.kem_ciphertext.deref =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok kemSecret))
    (hKemSecretZ :
      tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleEstablishResponder.z32 kemSecret =
        Aeneas.Std.Result.ok kemSecretZ)
    (hSignedBytes :
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleEstablishResponder.z32
          signedSecret =
        Aeneas.Std.Result.ok signedBytes)
    (hSignedPrekey :
      tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes signedBytes = Aeneas.Std.Result.ok signedPrekey)
    (hShared :
      ∃ identityKey encapsulated,
        our.dh_key = Aeneas.Std.Result.ok identityKey ∧
          tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                Tacenta.UnitLifecycleEstablishResponder.z32 kemSecretZ =
              Aeneas.Std.Result.ok encapsulated ∧
            tacenta_session_unit.responder_shared_secret identityKey signedPrekey oneTime peerIdentity peerEphemeral
                encapsulated =
              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok shared))
    (hSecretZ :
      tacenta_session_unit.zeroize.Zeroizing.new Tacenta.UnitLifecycleEstablishResponder.z32 shared =
        Aeneas.Std.Result.ok secretZ)
    (hSecret :
      tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Tacenta.UnitLifecycleEstablishResponder.z32
          secretZ =
        Aeneas.Std.Result.ok secret)
    (hReplay :
      tacenta_session_unit.lifecycle.responder_replay_fingerprint store decoded.kem_prekey_id secret lastResort =
        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok replay))
    (hTripleSecret : Tacenta.UnitLifecycleEstablishResponder.fullSlice secret = Aeneas.Std.Result.ok tripleSecret)
    (hRatchetPublic : signedPrekey.public_key = Aeneas.Std.Result.ok ratchetPublic)
    (hRatchetBytes : ratchetPublic.as_bytes = Aeneas.Std.Result.ok ratchetBytes)
    (hTriple :
      tacenta_session_unit.tacenta_triple.State.init_receiver tripleSecret ratchetBytes
          tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta =
        Aeneas.Std.Result.ok triple)
    (hBraidSecret : Tacenta.UnitLifecycleEstablishResponder.fullSlice secret = Aeneas.Std.Result.ok braidSecret)
    (hBraid : tacenta_session_unit.tacenta_braid.Braid.responder braidSecret = Aeneas.Std.Result.ok braid)
    (hRatchetPrivate :
      tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes signedBytes = Aeneas.Std.Result.ok ratchetPrivate)
    (hOurPublic : our.public = Aeneas.Std.Result.ok ourPublic)
    (hIdentityAd : tacenta_session_unit.lifecycle.identity_ad peerIdentity ourPublic = Aeneas.Std.Result.ok identityAd)
    (hEphemeralCopy :
      Aeneas.Std.alloc.vec.CloneVec.clone Aeneas.Std.core.clone.CloneU8 decoded.ephemeral =
        Aeneas.Std.Result.ok ephemeralCopy) :
    Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts

/--
info: def Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.session : {our :
    tacenta_session_unit.lifecycle.Identity} →
  {store : tacenta_session_unit.lifecycle.PrekeyStore} →
    {msg : Aeneas.Std.Slice Aeneas.Std.U8} →
      Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg →
        tacenta_session_unit.lifecycle.Session :=
fun {our} {store} {msg} p =>
  { triple := p.triple, braid := p.braid, ratchet_private := p.ratchetPrivate, identity_ad := p.identityAd,
    our_identity_public := p.ourPublic, peer_identity_public := p.peerIdentity, pending_initial := none,
    established_ephemeral := some p.ephemeralCopy }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.session

/--
info: def Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.message : {our :
    tacenta_session_unit.lifecycle.Identity} →
  {store : tacenta_session_unit.lifecycle.PrekeyStore} →
    {msg : Aeneas.Std.Slice Aeneas.Std.U8} →
      Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg → Aeneas.Std.Slice Aeneas.Std.U8 :=
fun {our} {store} {msg} p => p.decoded.message.deref
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts.message

/--
info: def Tacenta.UnitLifecycleEstablishResponder.ResponderCommit : tacenta_session_unit.lifecycle.PrekeyStore →
  Aeneas.Std.U32 →
    Aeneas.Std.U32 →
      Bool → Option (Aeneas.Std.Array Aeneas.Std.U8 32#usize) → tacenta_session_unit.lifecycle.PrekeyStore → Prop :=
fun store kemId oneTimeId lastResort replay store' =>
  ∃ store1 store2,
    (if lastResort = true then store1 = store
      else ∃ x, store.take_one_time_kem kemId = Aeneas.Std.Result.ok (x, store1)) ∧
      (if (oneTimeId != tacenta_session_unit.serialization.ABSENT_ID) = true then
          ∃ b, store1.take_one_time oneTimeId = Aeneas.Std.Result.ok (b, store2)
        else store2 = store1) ∧
        match replay with
        | none => store' = store2
        | some fp =>
          ∃ count seen,
            store2.last_resort_seen_for kemId = Aeneas.Std.Result.ok count ∧
              count < tacenta_session_unit.lifecycle.MAX_LAST_RESORT_SEEN ∧
                store2.last_resort_seen.push (kemId, fp) = Aeneas.Std.Result.ok seen ∧
                  store' =
                    { identity_public := store2.identity_public, signed_prekey_secret := store2.signed_prekey_secret,
                      signed_prekey_id := store2.signed_prekey_id, signed_prekey_sig := store2.signed_prekey_sig,
                      one_time := store2.one_time, kem := store2.kem, kem_id := store2.kem_id,
                      kem_sig := store2.kem_sig, kem_one_time := store2.kem_one_time,
                      previous_signed_prekey := store2.previous_signed_prekey, previous_kem := store2.previous_kem,
                      next_id := store2.next_id, last_resort_seen := seen,
                      legacy_last_resort_blocked := store2.legacy_last_resort_blocked }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.ResponderCommit

/--
info: def Tacenta.UnitLifecycleEstablishResponder.PrepareRefusal : tacenta_session_unit.lifecycle.Error → Prop :=
fun e =>
  (∃ d, e = tacenta_session_unit.lifecycle.Error.Decode d) ∨
    e = tacenta_session_unit.lifecycle.Error.UnknownPrekeyId ∨
      e = tacenta_session_unit.lifecycle.Error.LegacyLastResortRecord ∨
        e = tacenta_session_unit.lifecycle.Error.BadEncoding ∨
          e = tacenta_session_unit.lifecycle.Error.Handshake tacenta_session_unit.SessionError.InvalidIdentityKey ∨
            e =
                tacenta_session_unit.lifecycle.Error.Handshake
                  tacenta_session_unit.SessionError.NonContributoryAgreement ∨
              e = tacenta_session_unit.lifecycle.Error.Kem ∨
                e = tacenta_session_unit.lifecycle.Error.ReplayedLastResort ∨
                  e = tacenta_session_unit.lifecycle.Error.LastResortRecordFull
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.PrepareRefusal

/--
info: def Tacenta.UnitLifecycleEstablishResponder.responderChains : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize →
    Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U64 × tacenta_session_unit.tacenta_spqr.Chains) :=
fun c1 c2 =>
  Tacenta.UnitHeadroomSatisfiable.vecOf
    [(0#u64, { send := some { ck := c2, n := 0#u64 }, receive := some { ck := c1, n := 0#u64 } })] ⋯
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.responderChains

/--
info: def Tacenta.UnitLifecycleEstablishResponder.responderTriple : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize →
    Aeneas.Std.Array Aeneas.Std.U8 32#usize →
      Aeneas.Std.Array Aeneas.Std.U8 32#usize →
        Aeneas.Std.Array Aeneas.Std.U8 32#usize → tacenta_session_unit.tacenta_triple.State :=
fun a rk prk c1 c2 =>
  {
    classical :=
      { dhs_pub := a, dhr_pub := none, rk := rk, cks := none, ckr := none, ns := 0#u32, nr := 0#u32, pn := 0#u32,
        skipped := Aeneas.Std.alloc.vec.Vec.new tacenta_session_unit.tacenta_ratchet.SkippedKey, events := 0#u32,
        labels := tacenta_session_unit.tacenta_ratchet.LabelSet.Tacenta },
    post_quantum :=
      { rk := prk, epoch := 0#u64, chains := Tacenta.UnitLifecycleEstablishResponder.responderChains c1 c2,
        skipped := Aeneas.Std.alloc.vec.Vec.new tacenta_session_unit.tacenta_spqr.Skipped,
        direction := tacenta_session_unit.tacenta_spqr.Direction.B2a } }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.responderTriple

/--
info: def Tacenta.UnitLifecycleEstablishResponder.responderModelOf : {our : tacenta_session_unit.lifecycle.Identity} →
  {store : tacenta_session_unit.lifecycle.PrekeyStore} →
    {msg : Aeneas.Std.Slice Aeneas.Std.U8} →
      Tacenta.UnitLifecycleT3.DhView →
        Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg → Model.Lifecycle.Session :=
fun {our} {store} {msg} dh p =>
  {
    triple :=
      { classical := Tacenta.SessionUnitTripleT3.ratchetAbs p.triple.classical,
        postQuantum := Tacenta.SessionUnitTripleT3.spqrAbs p.triple.post_quantum },
    braid := Model.Braid.initBob (Tacenta.UnitLifecycleT3.sliceOf p.braidSecret),
    ratchetPrivate := dh.privateKey p.ratchetPrivate, identityAd := Tacenta.UnitLifecycleT3.vecOf p.identityAd,
    ourIdentityPublic := dh.publicKey p.ourPublic, peerIdentityPublic := dh.publicKey p.peerIdentity,
    pendingInitial := none, establishedEphemeral := some (Tacenta.UnitLifecycleT3.vecOf p.ephemeralCopy) }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.responderModelOf

/--
info: def Tacenta.UnitLifecycleEstablishResponder.basePointBytes : List UInt8 :=
9 :: List.replicate 31 0
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.basePointBytes

/--
info: def Tacenta.UnitLifecycleEstablishResponder.wireKey : List UInt8 :=
Model.Messages.ecCurveByte :: Tacenta.UnitLifecycleEstablishResponder.basePointBytes
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.wireKey

/--
info: def Tacenta.UnitLifecycleEstablishResponder.zeroWire : List UInt8 :=
Model.Messages.ecCurveByte :: List.replicate 32 0
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.zeroWire

/--
info: def Tacenta.UnitLifecycleEstablishResponder.ephKey : Bool → List UInt8 :=
fun zeroEph =>
  if zeroEph = true then Tacenta.UnitLifecycleEstablishResponder.zeroWire
  else Tacenta.UnitLifecycleEstablishResponder.wireKey
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.ephKey

/--
info: def Tacenta.UnitLifecycleEstablishResponder.successBytes : Bool →
  Aeneas.Std.Slice Aeneas.Std.U8 → Aeneas.Std.Slice Aeneas.Std.U8 → List UInt8 :=
fun zeroEph ct frame =>
  Model.Messages.encodeInitial Tacenta.UnitLifecycleEstablishResponder.wireKey
    (Tacenta.UnitLifecycleEstablishResponder.ephKey zeroEph) (Tacenta.UnitLifecycleT3.sliceOf ct) 0 0 0
    (Tacenta.UnitLifecycleT3.sliceOf frame)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.successBytes

/--
info: def Tacenta.UnitLifecycleEstablishResponder.successMessage : Bool →
  (ct frame : Aeneas.Std.Slice Aeneas.Std.U8) →
    (↑ct).length ≤ 4096 → (↑frame).length ≤ 4096 → Aeneas.Std.Slice Aeneas.Std.U8 :=
fun zeroEph ct frame hct hframe =>
  Tacenta.UnitSatisfiabilityBraidStates.sliceOfBytes
    (Tacenta.UnitLifecycleEstablishResponder.successBytes zeroEph ct frame) ⋯
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.successMessage

/--
info: def Tacenta.UnitLifecycleEstablishResponder.basePoint : Aeneas.Std.Array Aeneas.Std.U8 32#usize :=
⟨9#u8 :: List.replicate 31 0#u8, Tacenta.UnitLifecycleEstablishResponder.basePoint_length⟩
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.basePoint

/--
info: structure Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape (I : Tacenta.UnitSatisfiabilityJoint.Interp) :
  Prop
number of parameters: 1
fields:
  Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape.key : ∃ pkb,
      I.dhPubFromBytes Tacenta.UnitLifecycleEstablishResponder.basePoint = Aeneas.Std.Result.ok pkb ∧
        I.dhPubAsBytes pkb = Aeneas.Std.Result.ok Tacenta.UnitLifecycleEstablishResponder.basePoint ∧
          I.dhIsPrimeOrderPublic pkb = Aeneas.Std.Result.ok true ∧
            ∀ (k : I.PrivateKey), ∃ x, I.dhPrivAgree k pkb = Aeneas.Std.Result.ok (some x)
  Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape.kem : ∃ kp ct ss,
      (↑ct).length ≤ 4096 ∧ I.kemDecapsulate kp ct.deref = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ss)
  Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape.oneTime : Nonempty
      (I.Zeroizing (Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 32#usize)))
constructor:
  Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape.mk {I : Tacenta.UnitSatisfiabilityJoint.Interp}
    (key :
      ∃ pkb,
        I.dhPubFromBytes Tacenta.UnitLifecycleEstablishResponder.basePoint = Aeneas.Std.Result.ok pkb ∧
          I.dhPubAsBytes pkb = Aeneas.Std.Result.ok Tacenta.UnitLifecycleEstablishResponder.basePoint ∧
            I.dhIsPrimeOrderPublic pkb = Aeneas.Std.Result.ok true ∧
              ∀ (k : I.PrivateKey), ∃ x, I.dhPrivAgree k pkb = Aeneas.Std.Result.ok (some x))
    (kem :
      ∃ kp ct ss,
        (↑ct).length ≤ 4096 ∧ I.kemDecapsulate kp ct.deref = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok ss))
    (oneTime :
      Nonempty (I.Zeroizing (Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 32#usize)))) :
    Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape I
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.ResponderSuccessShape

/--
info: def Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape : Tacenta.UnitSatisfiabilityJoint.Interp → Prop :=
fun I =>
  ∃ z,
    I.dhPubFromBytes Tacenta.UnitSatisfiabilityBraidStates.zeros32 = Aeneas.Std.Result.ok z ∧
      ∀ (k : I.PrivateKey), I.dhPrivAgree k z = Aeneas.Std.Result.ok none
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.ZeroKeyShape

/--
info: def Tacenta.UnitLifecycleEstablishResponder.successStore : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes →
  tacenta_session_unit.zeroize.Zeroizing
      (Aeneas.Std.alloc.vec.Vec (Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 32#usize)) →
    tacenta_session_unit.tacenta_boundary.kem.KeyPair → tacenta_session_unit.lifecycle.PrekeyStore :=
fun pkb z kp =>
  { identity_public := pkb, signed_prekey_secret := Tacenta.UnitSatisfiabilityBraidStates.zeros32,
    signed_prekey_id := 0#u32, signed_prekey_sig := Aeneas.Std.Array.repeat 64#usize 0#u8, one_time := z, kem := kp,
    kem_id := 0#u32, kem_sig := Aeneas.Std.Array.repeat 64#usize 0#u8,
    kem_one_time :=
      Aeneas.Std.alloc.vec.Vec.new
        (Aeneas.Std.U32 × tacenta_session_unit.tacenta_boundary.kem.KeyPair × Aeneas.Std.Array Aeneas.Std.U8 64#usize),
    previous_signed_prekey := none, previous_kem := none, next_id := 1#u32,
    last_resort_seen := Aeneas.Std.alloc.vec.Vec.new (Aeneas.Std.U32 × Aeneas.Std.Array Aeneas.Std.U8 32#usize),
    legacy_last_resort_blocked := Aeneas.Std.alloc.vec.Vec.new Aeneas.Std.U32 }
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.successStore

/--
info: structure Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (our : tacenta_session_unit.lifecycle.Identity)
  (store : tacenta_session_unit.lifecycle.PrekeyStore) (msg : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) : Prop
number of parameters: 11
fields:
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.oracleOf : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
      rngCore cryptoRng dh trace oracle
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.codec : Tacenta.UnitLifecycleT3.DhCodecOf dh
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts
      rngCore
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.derivedKeys : Nonempty
      Tacenta.SessionUnitT1.DerivedKeysModel
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
      oracle.braidKem
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.dhPublicValid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.optionEq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.returns : ∃ out,
      tacenta_session_unit.lifecycle.establish_responder rngCore cryptoRng our store msg rng = Aeneas.Std.Result.ok out
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.trace_eq : trace rng = oracle.draws
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.inputs : ∀
      (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
      Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace p.session
        (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) p.message rng
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.reaches : Nonempty
      (Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg)
constructor:
  Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses.mk {R : Type}
    {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {our : tacenta_session_unit.lifecycle.Identity}
    {store : tacenta_session_unit.lifecycle.PrekeyStore} {msg : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R}
    (oracleOf : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : Tacenta.UnitLifecycleT3.DhCodecOf dh) (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    (derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel)
    (agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem)
    (dhPublicValid : Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid)
    (optionEq :
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
        @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq)
    (divCeil : Tacenta.SessionUnitDecoderBound.DivCeilValue)
    (returns :
      ∃ out,
        tacenta_session_unit.lifecycle.establish_responder rngCore cryptoRng our store msg rng =
          Aeneas.Std.Result.ok out)
    (trace_eq : trace rng = oracle.draws)
    (inputs :
      ∀ (p : Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg),
        Tacenta.UnitLifecycleDecryptRunBounds.DecryptRatchetRunInputs view oracle trace p.session
          (Tacenta.UnitLifecycleEstablishResponder.responderModelOf dh p) p.message rng)
    (reaches : Nonempty (Tacenta.UnitLifecycleEstablishResponder.ResponderPreparedParts our store msg)) :
    Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses rngCore cryptoRng trace dh view oracle our store
      msg rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.ResponderRouteHypotheses

/--
info: def Tacenta.UnitLifecycleEstablishResponder.otherThan : Aeneas.Std.Array Aeneas.Std.U8 32#usize →
  Aeneas.Std.Array Aeneas.Std.U8 32#usize :=
fun fp =>
  if fp = Tacenta.UnitSatisfiabilityBraidStates.zeros32 then Aeneas.Std.Array.repeat 32#usize 1#u8
  else Tacenta.UnitSatisfiabilityBraidStates.zeros32
-/
#guard_msgs in
#print Tacenta.UnitLifecycleEstablishResponder.otherThan
