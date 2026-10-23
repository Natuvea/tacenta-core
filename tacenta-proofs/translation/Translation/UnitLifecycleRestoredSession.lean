import Translation.UnitLifecycleEstablishedDecrypt
import Translation.UnitLifecycleSessionRoundTrip

/-!
# A restored session, from the bytes `import` accepted to the next `decrypt`

## The four named items

1. **The bytes and the result.**  For every byte string `b` and every session `s` with
   `lifecycle.Session.import b = ok (.Ok s)`.  `import` takes no randomness; its success form is that
   one.
2. **The model state from the same bytes.**  `restoredModelOf dh s`, a function of `s` and so of `b`
   (`import` is a function): the same reading as `establishedModelOf`.  It is not the model's own
   imported session: `Model.Lifecycle` has none (`Model.PersistedState.SessionState.ofBytes` returns the
   stored format, whose Braid is bytes), so no theorem here relates `b` to a model decoder.
3. **The relation and the invariant.**  `import_ok_gives_invariant` (no hypothesis): every accepted session
   passes `Session::invariant`.  `sessionRefines_restored`: in scope (`RestoredScope`: the Braid is in
   `KeysUnsampled` or `Failed`), `SessionRefines dh K s (restoredModelOf dh s)` for every DH view and KEM;
   **this holds by definition**, as at an established session; `sessionRefines_restored_unique`: it is the
   only related model session.
4. **What the next operation consumes, separated from what acceptance guarantees.**  Of what the next
   operation consumes, acceptance gives only the invariant (it also gives that `export` writes the accepted
   bytes back, the `NonCanonical` check).  It does not give the scope or `CounterHeadroom`:
   `counterHeadroom_iff_check` states the ceilings, for every session and so for every accepted one, as the
   decidable check `headroomCheck s`, and `invariant_does_not_give_counterHeadroom` (of
   `UnitLifecycleDecryptRunBounds`) shows a session with the classical clock parked at `u32::MAX - 1`
   passes the invariant.  `RestoredDecryptHypotheses` packs the
   accepted import, the scope, the ceilings and the caller's boundary records, trace equation, frame type,
   chunk relation and draw; `RestoredDecryptHypotheses.refines` and `restored_decrypt_refines` conclude
   that the public `Session::decrypt` on that ratchet-type frame refines `Model.Lifecycle.decrypt` at
   `restoredModelOf dh s`, refusals included.

## The real round trip

`export_import_established`: for every success output `s` of `establish_initiator_for`, `import` of
`export s` accepts and returns `s` itself, every field equal (no field differs: the private key and the
three public keys come back through the byte-codec laws, everything else is read back by the translated
decoders, `UnitLifecycleSessionRoundTrip.export_import_of_shape`).  So the restored copy is in scope and
meets `CounterHeadroom` (`restored_established_continues`), and `restored_established_initiator_decrypt_refines`
applies `restored_decrypt_refines` to it.  This is the theorem form of what
`tacenta-core/tests/restored_initiator_receives_reply.rs` tests: a copy of the established session,
exported and imported, receives the peer's ratchet frames.  `restored_established_inhabited` shows such a
success exists under the initiator axiom base and `InitiatorSuccessShape`; `restored_laws_model` shows the
laws of the round trip hold together in one model.  For the composition with `decrypt`,
`restored_decrypt_hypotheses_jointly_satisfiable` fills every field of `RestoredDecryptHypotheses` at once,
at the real constants, under the decrypt laws, the initiator contract axioms, `InitiatorSuccessShape` and the
nine laws of the round trip; `restored_decrypt_laws_model` shows that whole premise list holds in one
interpretation, `Interp.modelEstablished` (`restored_laws_model_established` is its round-trip half).

## Laws

The round trip takes nine assumed laws: the five of `UnitLifecycleSessionCodec` and `KemCiphertextLenBound`
(the ML-KEM ciphertext length constant is at most 65536, so the pending ciphertext's length prefix and the
size arithmetic of `export` do not wrap), with `KemCiphertextLenOf`, `DhPublicValid` and `OptionEqU64Shape`
from the established invariant.  Each has a model, and all nine hold with the decrypt laws in one
interpretation (`restored_decrypt_laws_model`).

## What it does not show

* A restored Braid holding a KEM value (a key pair restored by `IncrementalKeyPair::from_bytes` or a
  state restored by `EncapsState::from_bytes` has no model value at the wrapper's KEM model) or an erasure
  encoder or decoder (whose relations record a history a restored value does not have): outside the
  scope, so no relation is claimed there.
* The model's own imported session; initial-type frames; `encrypt`; the responder; the T3 refinement of
  establishment against `Model.Lifecycle.establishInitiator`.
* That `import` accepts a session that fails `CounterHeadroom`: the parked session is shown to pass the
  invariant, not shown to round-trip.
* That the real functions meet the laws, the boundary records, the chunk relation or the draw.
-/

namespace Tacenta.UnitLifecycleRestoredSession

open Aeneas Aeneas.Std Result
open tacenta_session_unit
open Tacenta.UnitLifecycleT3
open Tacenta.UnitLifecycleDecryptRatchetT3
open Tacenta.UnitLifecycleDecryptRunBounds
open Tacenta.UnitLifecycleEstablishInitiatorShape
open Tacenta.SessionUnitRatchetImportInv (bind_eq_ok_inv)

/-! ## Acceptance: what a successful `Session::import` guarantees -/

/-- **Every session `Session::import` accepts passes `Session::invariant`**, for every byte string.  The
generated body reaches `Ok` only through `let b1 ← invariant val; if b1`; every other branch returns an
`Err` (`TooShort`, `UnknownVersion`, `Malformed` through the decoder's own error, `NonCanonical`,
`Inconsistent`).  No hypothesis: the opaque functions inside the invariant are not evaluated, the
conclusion is what the code computed. -/
theorem import_ok_gives_invariant (b : Slice Std.U8) (s : lifecycle.Session)
    (h : lifecycle.Session.import b = ok (core.result.Result.Ok s)) :
    lifecycle.Session.invariant s = ok true := by
  unfold lifecycle.Session.import at h
  obtain ⟨r, -, h⟩ := bind_eq_ok_inv h
  rcases r with val | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    obtain ⟨z, -, h⟩ := bind_eq_ok_inv h
    obtain ⟨v, -, h⟩ := bind_eq_ok_inv h
    obtain ⟨sl, -, h⟩ := bind_eq_ok_inv h
    obtain ⟨c, -, h⟩ := bind_eq_ok_inv h
    split at h
    · simp at h
    · obtain ⟨b1, hb1, h⟩ := bind_eq_ok_inv h
      split at h
      · simp only [ok.injEq, core.result.Result.Ok.injEq] at h
        subst h
        simp_all
      · simp at h
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h

/-! ## Acceptance against continuation: the four counter ceilings -/

/-- The four counter ceilings of `CounterHeadroom` as one decidable check on the session's fields: the
classical clock, the sparse epoch, every sparse chain counter and the Braid epoch, each below its
ceiling. -/
def headroomCheck (s : lifecycle.Session) : Bool :=
  decide (s.triple.classical.events.val + 1 < Std.U32.max) &&
  decide (s.triple.post_quantum.epoch.val + 1 < Std.U64.max) &&
  s.triple.post_quantum.chains.val.all (fun p =>
    (match p.2.send with | some ch => decide (ch.n.val < Std.U64.max) | none => true) &&
    (match p.2.receive with | some ch => decide (ch.n.val < Std.U64.max) | none => true)) &&
  decide ((Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state).val + 1 < Std.U64.max)

/-- `CounterHeadroom` is exactly `headroomCheck`, for every session, so for every session `import` accepts.
Acceptance itself does not give it (`invariant_does_not_give_counterHeadroom`: a session with the classical
clock parked at `u32::MAX - 1` passes the invariant, and `import` checks nothing about counters beyond the
invariant); the check is not part of acceptance and is not added to it here. -/
theorem counterHeadroom_iff_check (s : lifecycle.Session) :
    CounterHeadroom s ↔ headroomCheck s = true := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    simp only [headroomCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, h4⟩
    intro p hp
    refine ⟨?_, ?_⟩
    · cases hs : p.2.send with
      | none => rfl
      | some ch => simpa using h3 p hp ch (Or.inl hs)
    · cases hr : p.2.receive with
      | none => rfl
      | some ch => simpa using h3 p hp ch (Or.inr hr)
  · intro h
    simp only [headroomCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨h1, h2, ?_, h4⟩
    intro p hp ch hch
    obtain ⟨hs, hr⟩ := h3 p hp
    rcases hch with hch | hch
    · rw [hch] at hs; simpa using hs
    · rw [hch] at hr; simpa using hr

/-! ## The scope, the model state and the relation -/

/-- **The scope of the restored relation**: the session's Braid is in `KeysUnsampled` or `Failed`.  These
are the two Braid states that hold neither a KEM value (`IncrementalKeyPair`, `EncapsState`) nor an erasure
encoder or decoder.  `Session::invariant` accepts a failed Braid (the failure is terminal and persists; the
epoch relation and the Braid's half of the role rule are not checked for it), so `import` can return one.
Excluded, and why:
* the seven states holding a key pair or an encapsulation state (`KeysSampled`, `HeaderSent`,
  `Ct1Received`, `EkSentCt1Received`, `Ct1Sampled`, `EkReceivedCt1Sampled`, `Ct1Acknowledged`): a key pair
  restored by `IncrementalKeyPair::from_bytes` or a state restored by `EncapsState::from_bytes` has no
  model value at the wrapper's KEM model (`UnitKemWrapperModel`), and `KeyPairRefines`/`EncapsRefines` are
  behaviour relations over the opaque value;
* `Ct2Sampled`, `NoHeaderReceived`, `HeaderReceived`, which hold an erasure encoder or decoder and no KEM
  value: `EncoderRefines` records where an encoder came from (a source slice and a number of steps) and
  `DecoderRefines` how a decoder answers future chunks against one source; a restored encoder or decoder
  has no such history, and no law here gives one.
In practice the scope is narrow: the first send from `KeysUnsampled` moves the Braid to `KeysSampled`
(`tacenta-core/braid/src/lib.rs:706-724`), a responder starts in `NoHeaderReceived`, and a Braid returns to
`KeysUnsampled` only on the side that sent the last ciphertext, when the next epoch begins
(`lib.rs:1355-1368`).  So the scope holds a snapshot taken on that side before its first send in the epoch
(at epoch 1, the established initiator) and a failed session; most mid-conversation snapshots are outside
it. -/
def RestoredScope (s : lifecycle.Session) : Prop :=
  (∃ epoch auth, s.braid.state = tacenta_braid.State.KeysUnsampled epoch auth) ∨
    s.braid.state = tacenta_braid.State.Failed

/-- **The model session a restored session in scope stands for**, read off the decoded session: the
Triple through `ratchetAbs`/`spqrAbs`, the Braid through `unsampledModelOf` (`KeysUnsampled e a` to
`keysUnsampled e (AuthOf a)`, `Failed` to `failed`), the six other fields through the DH view.  It is the
same reading as `establishedModelOf`.  It is not the model's own imported session: `Model.Lifecycle` has
none (`Model.PersistedState.SessionState.ofBytes` returns the stored format, whose Braid is bytes), so this
is a function of the decoded state and hence of the accepted bytes. -/
def restoredModelOf (dh : DhView) (s : lifecycle.Session) : Model.Lifecycle.Session :=
  establishedModelOf dh s

/-- A session in scope refines `restoredModelOf`, for every DH view and KEM.  **By definition**: each field
of `SessionRefines` is an equation through the abstraction functions, the `KeysUnsampled` arm of the Braid
relation compares the epoch and the authenticator, which `unsampledModelOf` copies, and the `Failed` arm is
`True`. -/
theorem sessionRefines_restored (dh : DhView) (K : Model.Braid.Kem) (s : lifecycle.Session)
    (hscope : RestoredScope s) : SessionRefines dh K s (restoredModelOf dh s) := by
  refine ⟨⟨rfl, rfl⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases hscope with ⟨epoch, auth, hb⟩ | hb
  · simp only [restoredModelOf, establishedModelOf, hb, unsampledModelOf,
      Tacenta.SessionUnitBraidT3.StateRefines, and_self]
  · simp only [restoredModelOf, establishedModelOf, hb, unsampledModelOf,
      Tacenta.SessionUnitBraidT3.StateRefines]

/-- **`restoredModelOf` is the only model session a session in scope refines**, for every DH view and
KEM. -/
theorem sessionRefines_restored_unique (dh : DhView) (K : Model.Braid.Kem) (s : lifecycle.Session)
    (hscope : RestoredScope s) (m : Model.Lifecycle.Session) (hrel : SessionRefines dh K s m) :
    m = restoredModelOf dh s := by
  obtain ⟨⟨htc, htp⟩, hbr, hrp, had, hour, hpeer, hpend, hest⟩ := hrel
  obtain ⟨⟨mc, mp⟩, mb, mrp, mad, mour, mpeer, mpend, mest⟩ := m
  simp only at htc htp hbr hrp had hour hpeer hpend hest
  subst htc htp hrp had hour hpeer hpend hest
  rcases hscope with ⟨epoch, auth, hb⟩ | hb
  · rw [hb] at hbr
    cases mb with
    | keysUnsampled e a =>
        obtain ⟨he, ha⟩ := hbr
        subst he ha
        simp [restoredModelOf, establishedModelOf, hb, unsampledModelOf]
    | _ => simp [Tacenta.SessionUnitBraidT3.StateRefines] at hbr
  · rw [hb] at hbr
    cases mb with
    | failed => simp [restoredModelOf, establishedModelOf, hb, unsampledModelOf]
    | _ => simp [Tacenta.SessionUnitBraidT3.StateRefines] at hbr

/-- `HonestChunk` holds at the model state of every session in scope, for every model message: the model
Braid is `keysUnsampled` or `failed`, neither of which holds a decoder, so the condition is `True`. -/
theorem honestChunk_restored (dh : DhView) (s : lifecycle.Session) (hscope : RestoredScope s)
    (msg : Model.Braid.Msg) :
    Tacenta.SessionUnitBraidT3.HonestChunk (restoredModelOf dh s).braid msg := by
  intro mc _ _
  rcases hscope with ⟨epoch, auth, hb⟩ | hb <;>
    simp [restoredModelOf, establishedModelOf, hb, unsampledModelOf]

/-! ## Continuation: `decrypt` at an accepted session in scope -/

/-- **The hypotheses of the `decrypt_ratchet` refinement at an accepted import in scope**, for one
choice of every binder.  The session's part of acceptance is `accepted`; the scope and the ceilings are
the two premises acceptance does not give and the next operation consumes (`scope`, `counters`; the
latter is `headroomCheck s = true`, `counterHeadroom_iff_check`).  The boundary records, the trace
equation, the frame's type, the chunk relation and the draw are the caller's, as
`decrypt_ratchet_refines_of_invariant` takes them. -/
structure RestoredDecryptHypotheses {R : Type} (rngCore : rand_core_1.RngCore R)
    (cryptoRng : rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle) (bytes : Slice Std.U8)
    (s : lifecycle.Session) (message : Slice Std.U8) (rng : R) : Prop where
  accepted : lifecycle.Session.import bytes = ok (core.result.Result.Ok s)
  scope : RestoredScope s
  counters : CounterHeadroom s
  oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle
  codec : DhCodecOf dh
  contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore
  derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel
  agreements : DecryptRatchetAgreements oracle.braidKem
  messageType : serialization.message_type message = ok (some serialization.MessageType.Ratchet)
  trace_eq : trace rng = oracle.draws
  chunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelComposite, ciphertext) →
      CompositeRefines realComposite modelComposite →
      IncomingChunkRefines view (restoredModelOf dh s).braid realComposite modelComposite
  draw : ∃ draw rest, trace rng = draw :: rest

/-- From the record, every hypothesis of `decrypt_ratchet_refines_of_invariant` at the restored session
and `restoredModelOf dh s`: the invariant from acceptance (`import_ok_gives_invariant`), the relation from
the scope (`sessionRefines_restored`), `HonestChunk` from the scope (`honestChunk_restored`), the ceilings
and the rest from the record. -/
theorem RestoredDecryptHypotheses.ofInvariant {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle} {bytes : Slice Std.U8}
    {s : lifecycle.Session} {message : Slice Std.U8} {rng : R}
    (h : RestoredDecryptHypotheses rngCore cryptoRng trace dh view oracle bytes s message rng) :
    DecryptOfInvariantHypotheses rngCore cryptoRng trace dh view oracle s (restoredModelOf dh s)
      message rng :=
  { oracleOf := h.oracleOf
    codec := h.codec
    contracts := h.contracts
    derivedKeys := h.derivedKeys
    agreements := h.agreements
    invariant := import_ok_gives_invariant bytes s h.accepted
    related := sessionRefines_restored dh oracle.braidKem s h.scope
    counters := h.counters
    trace_eq := h.trace_eq
    inputs :=
      { chunk := h.chunk
        honest := fun _ _ _ => honestChunk_restored dh s h.scope _
        draw := h.draw } }

/-- **The public `Session::decrypt` at an accepted import in scope refines the model's `decrypt`**, for
every ratchet-type frame: under the record, `decrypt` at `s` returns and its result, post-state and draws
left refine `Model.Lifecycle.decrypt` at `restoredModelOf dh s`, refusals included.  Composes
`decrypt_ratchet_refines_of_invariant` (through `DecryptOfInvariantHypotheses.refines`) with
`decrypt_ratchet_message_refines`. -/
theorem RestoredDecryptHypotheses.refines {R : Type} {rngCore : rand_core_1.RngCore R}
    {cryptoRng : rand_core_1.CryptoRng R} {trace : R → List Model.Lifecycle.Key} {dh : DhView}
    {view : Model.Lifecycle.CodewordView} {oracle : Model.Lifecycle.Oracle} {bytes : Slice Std.U8}
    {s : lifecycle.Session} {message : Slice Std.U8} {rng : R}
    (h : RestoredDecryptHypotheses rngCore cryptoRng trace dh view oracle bytes s message rng) :
    PublicDecryptWitness rngCore cryptoRng trace dh oracle.braidKem view oracle s
      (restoredModelOf dh s) message rng := by
  obtain ⟨output, hout, hstep⟩ := h.ofInvariant.refines
  exact decrypt_ratchet_message_refines rngCore cryptoRng trace dh oracle.braidKem view oracle s
    (restoredModelOf dh s) message rng output h.messageType hout hstep

/-- **`restored_decrypt_refines`**: for every byte string `bytes` that `Session::import` accepts with
session `s` in scope and with `CounterHeadroom s`, the public `Session::decrypt` on every ratchet-type
frame refines the model's `decrypt` at `restoredModelOf dh s`, under the caller's boundary records, trace
equation, chunk relation and draw.  The same as `RestoredDecryptHypotheses.refines`, with the hypotheses
spelled out. -/
theorem restored_decrypt_refines {R : Type}
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (bytes : Slice Std.U8) (s : lifecycle.Session)
    (h : lifecycle.Session.import bytes = ok (core.result.Result.Ok s))
    (hscope : RestoredScope s) (hcounters : CounterHeadroom s)
    (message : Slice Std.U8) (rng : R)
    (htype : serialization.message_type message = ok (some serialization.MessageType.Ratchet))
    (htrace : trace rng = oracle.draws)
    (hchunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelComposite, ciphertext) →
      CompositeRefines realComposite modelComposite →
      IncomingChunkRefines view (restoredModelOf dh s).braid realComposite modelComposite)
    (hdraw : ∃ draw rest, trace rng = draw :: rest) :
    PublicDecryptWitness rngCore cryptoRng trace dh oracle.braidKem view oracle s
      (restoredModelOf dh s) message rng :=
  RestoredDecryptHypotheses.refines
    { accepted := h, scope := hscope, counters := hcounters, oracleOf := oracleOf, codec := codec,
      contracts := contracts, derivedKeys := ⟨inferInstance⟩, agreements := agreements,
      messageType := htype, trace_eq := htrace, chunk := hchunk, draw := hdraw }

/-! ## The real round trip: a persisted copy of an established initiator -/

open Tacenta.UnitLifecycleSessionCodec
open Tacenta.UnitLifecycleSessionRoundTrip

/-- The ML-KEM ciphertext length constant is at most 65536, as a shape over the constant.  True of the
boundary by reading (`tacenta-core/boundary/src/kem.rs`: `ciphertext_len` is the length of an
ML-KEM-1024 ciphertext, 1568 bytes). -/
def KemCiphertextLenBoundShape (ciphertextLen : Result Usize) : Prop :=
  ∃ n : Usize, ciphertextLen = ok n ∧ n.val ≤ 65536

/-- The law at the real constant. -/
def KemCiphertextLenBound : Prop := KemCiphertextLenBoundShape tacenta_boundary.kem.ciphertext_len

/-- A model, at the constant the established-initiator joint model uses (`ok 0`). -/
theorem model_kemCiphertextLenBound : KemCiphertextLenBoundShape (ok 0#usize) :=
  ⟨0#usize, rfl, by simp⟩

/-- The session the parts of a successful `establish_initiator_for` make has the shape the round trip
covers: Braid `KeysUnsampled` at epoch 1, no stored key, the one sparse entry at epoch 0 with both chains
at counter 0, a pending initial message, no established ephemeral, associated data of 66 bytes and a
ciphertext of `kem::ciphertext_len` bytes. -/
theorem codecShape_parts (hpub : DhPublicBytesRoundTrip) (hct : KemCiphertextLenOf)
    (hbound : KemCiphertextLenBound) {R : Type} {rc : rand_core_1.RngCore R}
    {crc : rand_core_1.CryptoRng R} {our : lifecycle.Identity} {bundle : lifecycle.PublishedBundle}
    (p : InitiatorOutputParts rc crc our bundle) :
    CodecShape p.session 1#u64 p.auth 0#u64 { ck := p.sparseSend, n := 0#u64 }
      { ck := p.sparseReceive, n := 0#u64 }
      { ephemeral_public := p.ephemeralPublic, kem_ciphertext := p.kemCiphertext,
        signed_prekey_id := bundle.signed_prekey_id, one_time_prekey_id := bundle.one_time_prekey_id,
        kem_prekey_id := bundle.kem_prekey_id } := by
  obtain ⟨n, hn, hnle⟩ := hbound
  obtain ⟨n', hn', hlen⟩ := hct rc crc _ _ _ _ _ p.hEncapsulate
  rw [hn] at hn'
  cases hn'
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl⟩
  · intro h; have h1 := congrArg UScalar.val h; simp [core.num.U64.MAX, U64.rMax] at h1
  · simp [InitiatorOutputParts.session, initiatorTriple, initChains,
      Tacenta.UnitHeadroomSatisfiable.vecOf]
  · have := identity_ad_length_of hpub _ _ _ p.hIdentityAd
    simp only [InitiatorOutputParts.session]; omega
  · simp only; omega

/-- **`export_import_established` (the real round trip)**: for every success output `s` of
`establish_initiator_for`, `Session::export s` returns bytes that `Session::import` accepts, and the session
it returns is `s` itself, every field equal.  Under the laws of the round trip (`ZeroizingVecRoundTrip`,
`OptionBranchSome`, `VecAsSlice`, `DhPrivateBytesRoundTrip`, `DhPublicBytesRoundTrip`), the ciphertext
length laws (`KemCiphertextLenOf`, `KemCiphertextLenBound`) and the laws of the established invariant
(`DhPublicValid`, `OptionEqU64Shape`). -/
theorem export_import_established (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpubb : DhPublicBytesRoundTrip)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (hbound : KemCiphertextLenBound)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {E : Type} (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    ∃ z v, lifecycle.Session.export s = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok s) := by
  have hinv := establish_initiator_for_admissible rc crc hpub hct hoeq our bundle expected rng0 rng1 s h
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  exact export_import_of_shape hz hbr hsl hpriv hpubb p.session _ _ _ _ _ _
    (codecShape_parts hpubb hct hbound p) hinv

/-- **The restored copy of an established initiator meets every premise acceptance does not give**: for
every success output `s` of `establish_initiator_for`, the bytes `export` writes are accepted by `import`
with `s` itself, and that accepted session is in scope and meets `CounterHeadroom`. -/
theorem restored_established_continues (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpubb : DhPublicBytesRoundTrip)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (hbound : KemCiphertextLenBound)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    {E : Type} (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1)) :
    ∃ z v, lifecycle.Session.export s = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok s) ∧
      RestoredScope s ∧ CounterHeadroom s := by
  obtain ⟨z, v, hz', hv, himp⟩ := export_import_established hz hbr hsl hpriv hpubb hpub hct hbound hoeq
    rc crc our bundle expected rng0 rng1 s h
  obtain ⟨p, rfl⟩ := establish_initiator_for_parts rc crc our bundle expected rng0 rng1 s h
  exact ⟨z, v, hz', hv, himp, Or.inl ⟨_, _, rfl⟩, counterHeadroom_parts p⟩

/-- **`restored_established_initiator_decrypt_refines`**: for every success output `s` of
`establish_initiator_for`, the bytes `export` writes are accepted by `import` with `s` itself, and the
public `Session::decrypt` of the accepted session on every ratchet-type frame refines the model's `decrypt`
at `restoredModelOf dh s`, under the round-trip laws, the established invariant's laws and the caller's
decrypt boundary records, trace equation, chunk relation and draw.  The theorem form of the tested
reachability: a persisted copy of the established session, restored, receives the peer's ratchet frames
under the model's step, given the caller's boundary records, trace equation, chunk relation and draw. -/
theorem restored_established_initiator_decrypt_refines {R E : Type}
    (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpubb : DhPublicBytesRoundTrip)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (hbound : KemCiphertextLenBound)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (rngCore : rand_core_1.RngCore R) (cryptoRng : rand_core_1.CryptoRng R)
    (trace : R → List Model.Lifecycle.Key) (dh : DhView)
    (view : Model.Lifecycle.CodewordView) (oracle : Model.Lifecycle.Oracle)
    (oracleOf : DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : DhCodecOf dh)
    (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    [Tacenta.SessionUnitT1.DerivedKeysModel]
    (agreements : DecryptRatchetAgreements oracle.braidKem)
    (rc : rand_core_1.RngCore E) (crc : rand_core_1.CryptoRng E)
    (our : lifecycle.Identity) (bundle : lifecycle.PublishedBundle)
    (expected : tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E) (s : lifecycle.Session)
    (h : lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
      ok (core.result.Result.Ok s, rng1))
    (message : Slice Std.U8) (rng : R)
    (htype : serialization.message_type message = ok (some serialization.MessageType.Ratchet))
    (htrace : trace rng = oracle.draws)
    (hchunk : ∀ (realComposite : tacenta_wire.Composite)
      (modelComposite : Model.CompositeHeader.Composite) (ciphertext : Bytes),
      Model.CompositeHeader.decodeDetailed (sliceOf message) = .ok (modelComposite, ciphertext) →
      CompositeRefines realComposite modelComposite →
      IncomingChunkRefines view (restoredModelOf dh s).braid realComposite modelComposite)
    (hdraw : ∃ draw rest, trace rng = draw :: rest) :
    ∃ z v, lifecycle.Session.export s = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok s) ∧
      PublicDecryptWitness rngCore cryptoRng trace dh oracle.braidKem view oracle s
        (restoredModelOf dh s) message rng := by
  obtain ⟨z, v, hz', hv, himp, hscope, hcounters⟩ := restored_established_continues hz hbr hsl hpriv
    hpubb hpub hct hbound hoeq rc crc our bundle expected rng0 rng1 s h
  exact ⟨z, v, hz', hv, himp, restored_decrypt_refines rngCore cryptoRng trace dh view oracle oracleOf
    codec contracts agreements (alloc.vec.Vec.deref v) s himp hscope hcounters message rng htype htrace
    hchunk hdraw⟩

/-! ## Non-vacuity -/

open Tacenta.UnitSatisfiabilityJoint (Interp Interp.real Interp.model)

/-- **The round trip is not about an empty set**: under the initiator axiom base and
`InitiatorSuccessShape` (which give a successful establishment, `establish_initiator_for_succeeds`) and the
laws of `restored_established_continues`, for every identity and source there are a bundle and an
established session whose exported bytes `import` accepts with the session itself, in scope and with the
ceilings. -/
theorem restored_established_inhabited {R : Type} (rc : rand_core_1.RngCore R)
    (crc : rand_core_1.CryptoRng R)
    (axioms : Nonempty (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Interp.real rc))
    (succ : InitiatorSuccessShape Interp.real rc crc)
    (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome)
    (hsl : VecAsSlice) (hpriv : DhPrivateBytesRoundTrip) (hpubb : DhPublicBytesRoundTrip)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf) (hbound : KemCiphertextLenBound)
    (hoeq : Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
      (@core.option.Option.Insts.CoreCmpPartialEqOption.eq))
    (our : lifecycle.Identity) (rng0 : R) :
    ∃ (bundle : lifecycle.PublishedBundle) (s : lifecycle.Session) (rng1 : R)
      (z : zeroize.Zeroizing (alloc.vec.Vec U8)) (v : alloc.vec.Vec U8),
      lifecycle.establish_initiator_for rc crc our bundle bundle.bundle.identity_key rng0 =
        ok (core.result.Result.Ok s, rng1) ∧
      lifecycle.Session.export s = ok z ∧
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref vecInst z = ok v ∧
      lifecycle.Session.import (alloc.vec.Vec.deref v) = ok (core.result.Result.Ok s) ∧
      RestoredScope s ∧ CounterHeadroom s := by
  obtain ⟨bundle, s, rng1, h⟩ := establish_initiator_for_succeeds rc crc axioms succ our rng0
  obtain ⟨z, v, h1, h2, h3, h4, h5⟩ := restored_established_continues hz hbr hsl hpriv hpubb hpub hct
    hbound hoeq rc crc our bundle _ rng0 rng1 s h
  exact ⟨bundle, s, rng1, z, v, h, h1, h2, h3, h4, h5⟩

/-- **The laws of this piece hold together in one model**, with those of the established invariant: the
three byte-codec laws and `DhPublicValidShape`, `KemCiphertextLenLawShape` at `Interp.model`, `Option::branch`
and `Vec::as_slice` at their standard-library definitions, `Option::eq` at `optionEqImpl`, the ciphertext
length constant at `ok 0`.  Each is a statement over opaque constants that the real constants instantiate,
so this is an argument about derivations, not a statement that the real functions meet them. -/
theorem restored_laws_model :
    ZeroizingVecRoundTripShape Interp.model ∧ DhPrivateBytesRoundTripShape Interp.model ∧
      DhPublicBytesRoundTripShape Interp.model ∧ OptionBranchSomeShape @optionBranchImpl ∧
      VecAsSliceShape @vecAsSliceImpl ∧ KemCiphertextLenBoundShape (ok 0#usize) ∧
      DhPublicValidShape Interp.model ∧ KemCiphertextLenLawShape (ok 0#usize) Interp.model ∧
      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape (@Tacenta.UnitHeadroomInvariant.optionEqImpl) :=
  ⟨model_zeroizingVecRoundTrip, model_dhPrivateBytesRoundTrip, model_dhPublicBytesRoundTrip,
    (fun _ _ => rfl), vecAsSliceImpl_shape, model_kemCiphertextLenBound, model_dhPublicValid,
    model_kemCiphertextLen, Tacenta.UnitHeadroomInvariant.optionEqImpl_shape⟩

/-! ## The composed premise list holds together -/

open Tacenta.UnitLifecycleIntegrationScreen (byteRng byteCrc byteTrace)
open Tacenta.UnitSatisfiabilityJoint (InitiatorAxiom)
open Tacenta.UnitLifecycleEstablishedDecrypt (established_decrypt_hypotheses_jointly_satisfiable
  established_decrypt_laws_model viewEstablished)

/-- **The six laws of the round trip hold at the interpretation the decrypt joint model uses**,
`Interp.modelEstablished`: the three byte-codec laws there, `Option::branch` and `Vec::as_slice` at their
standard-library definitions, and the ciphertext length constant at `ok 0`, the constant
`established_decrypt_laws_model` uses for `KemCiphertextLenLawShape`.  In the substitution sense of
`UnitSatisfiabilityRecords`; not a statement that the real functions meet them. -/
theorem restored_laws_model_established :
    ZeroizingVecRoundTripShape Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      DhPrivateBytesRoundTripShape Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      DhPublicBytesRoundTripShape Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      OptionBranchSomeShape @optionBranchImpl ∧ VecAsSliceShape @vecAsSliceImpl ∧
      KemCiphertextLenBoundShape (ok 0#usize) :=
  ⟨fun _ _ => ⟨_, rfl, rfl⟩, fun _ => ⟨_, _, rfl, rfl, rfl⟩, fun _ => ⟨_, rfl, rfl⟩,
    (fun _ _ => rfl), vecAsSliceImpl_shape, model_kemCiphertextLenBound⟩

/-- **Every field of `RestoredDecryptHypotheses` holds together at the real constants**, under the decrypt
laws `DecryptJointLaws K dh` of `UnitLifecycleDecryptScreen`, the axiom part of the initiator contract
record and `InitiatorSuccessShape` at the byte-stream source, and the nine laws of the round trip, all
assumed: for every identity and codeword view there are an oracle with `braidKem = K`, a session and the
bytes `export` writes for it such that, at the sample ratchet frame and source of
`UnitLifecycleDecryptRatchetScreen`, `import` accepts the bytes with that session, the session is in scope
and meets `CounterHeadroom`, and every boundary record, the trace equation, the frame type, the chunk
relation and the draw hold.  The session is the established one of
`established_decrypt_hypotheses_jointly_satisfiable`, restored by `restored_established_continues`. -/
theorem restored_decrypt_hypotheses_jointly_satisfiable (K : Model.Braid.Kem) (dh : DhView)
    (L : Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh)
    (A : Nonempty (InitiatorAxiom Interp.real byteRng))
    (S : InitiatorSuccessShape Interp.real byteRng byteCrc)
    (hpub : DhPublicValid) (hct : KemCiphertextLenOf)
    (hz : ZeroizingVecRoundTrip) (hbr : OptionBranchSome) (hsl : VecAsSlice)
    (hpriv : DhPrivateBytesRoundTrip) (hpubb : DhPublicBytesRoundTrip) (hbound : KemCiphertextLenBound)
    (our : lifecycle.Identity) (view : Model.Lifecycle.CodewordView) :
    ∃ (oracle : Model.Lifecycle.Oracle) (s : lifecycle.Session) (v : alloc.vec.Vec U8),
      oracle.braidKem = K ∧
      RestoredDecryptHypotheses byteRng byteCrc byteTrace dh view oracle (alloc.vec.Vec.deref v) s
        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
        Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng := by
  obtain ⟨oracle, bundle, s, rng1, hK, H⟩ :=
    established_decrypt_hypotheses_jointly_satisfiable K dh L A S hpub hct our
  have H0 := H view
  obtain ⟨z, v, -, -, himp, hscope, hcounters⟩ := restored_established_continues hz hbr hsl hpriv hpubb
    hpub hct hbound L.optionEq byteRng byteCrc our bundle _ [] rng1 s H0.established
  exact ⟨oracle, s, v, hK,
    { accepted := himp, scope := hscope, counters := hcounters, oracleOf := H0.oracleOf,
      codec := H0.codec, contracts := H0.contracts, derivedKeys := H0.derivedKeys,
      agreements := H0.agreements, messageType := H0.messageType, trace_eq := H0.trace_eq,
      chunk := H0.chunk, draw := H0.draw }⟩

/-- **The whole premise list of the restored composition holds in one interpretation**,
`Interp.modelEstablished`, with its view, the KEM model `toyKem`, `optionEqImpl` for `Option::eq`, the
constant `ok 0` for `kem::ciphertext_len` (in both ciphertext laws) and the byte-stream source: the decrypt
laws, the initiator contract axioms, `InitiatorSuccessShape`, `DhPublicValid` and `KemCiphertextLenOf`
(`established_decrypt_laws_model`), and the six laws of the round trip (`restored_laws_model_established`),
that is, the shape of every hypothesis `restored_decrypt_hypotheses_jointly_satisfiable` takes.  In the
substitution sense of `UnitSatisfiabilityRecords`; not a statement that the real primitives meet them. -/
theorem restored_decrypt_laws_model :
    (Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
        Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished viewEstablished
        Model.Braid.toyKem @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
      Nonempty (InitiatorAxiom Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished byteRng) ∧
      InitiatorSuccessShape Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished byteRng
        byteCrc ∧
      DhPublicValidShape Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      KemCiphertextLenLawShape (ok 0#usize)
        Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished) ∧
    (ZeroizingVecRoundTripShape Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      DhPrivateBytesRoundTripShape Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      DhPublicBytesRoundTripShape Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      OptionBranchSomeShape @optionBranchImpl ∧ VecAsSliceShape @vecAsSliceImpl ∧
      KemCiphertextLenBoundShape (ok 0#usize)) :=
  ⟨established_decrypt_laws_model, restored_laws_model_established⟩

end Tacenta.UnitLifecycleRestoredSession

/-! ## Pins

The constants each result depends on, and the statement of each result and definition, held by the
build.  `attest.py` requires every one of them (`REQUIRED_PINS`, `REQUIRED_STATEMENT_PINS`,
`REQUIRED_PRINT_FORM`). -/

/--
info: 'Tacenta.UnitLifecycleRestoredSession.import_ok_gives_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.CT1_LEN,
 tacenta_session_unit.tacenta_kem.CT2_LEN,
 tacenta_session_unit.tacenta_kem.EK_VECTOR_LEN,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.HEADER_LEN,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.validate_ek,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
 tacenta_session_unit.core.num.Usize.div_ceil,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.from_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.public_key,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey.to_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.as_bytes,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.from_bytes,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.import_ok_gives_invariant

/--
info: 'Tacenta.UnitLifecycleRestoredSession.counterHeadroom_iff_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.counterHeadroom_iff_check

/--
info: 'Tacenta.UnitLifecycleRestoredSession.sessionRefines_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.sessionRefines_restored

/--
info: 'Tacenta.UnitLifecycleRestoredSession.sessionRefines_restored_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_kem.encapsulate2,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.alloc.vec.Vec.truncate,
 tacenta_session_unit.core.num.Usize.div_ceil]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.sessionRefines_restored_unique

/--
info: 'Tacenta.UnitLifecycleRestoredSession.honestChunk_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kem.EncapsState,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair,
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.honestChunk_restored

/--
info: 'Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.ofInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
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
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.ofInvariant

/--
info: 'Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
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
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.refines

/--
info: 'Tacenta.UnitLifecycleRestoredSession.restored_decrypt_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PrivateKey,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes,
 tacenta_session_unit.tacenta_boundary.dh.is_prime_order_public,
 tacenta_session_unit.tacenta_boundary.kem.ciphertext_len,
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
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
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.restored_decrypt_refines

/--
info: 'Tacenta.UnitLifecycleRestoredSession.model_kemCiphertextLenBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.model_kemCiphertextLenBound

/--
info: 'Tacenta.UnitLifecycleRestoredSession.codecShape_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.codecShape_parts

/--
info: 'Tacenta.UnitLifecycleRestoredSession.export_import_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
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
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.export_import_established

/--
info: 'Tacenta.UnitLifecycleRestoredSession.restored_established_continues' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
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
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.restored_established_continues

/--
info: 'Tacenta.UnitLifecycleRestoredSession.restored_established_initiator_decrypt_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
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
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.restored_established_initiator_decrypt_refines

/--
info: 'Tacenta.UnitLifecycleRestoredSession.restored_established_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
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
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.restored_established_inhabited

/--
info: 'Tacenta.UnitLifecycleRestoredSession.restored_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.restored_laws_model

/--
info: 'Tacenta.UnitLifecycleRestoredSession.restored_laws_model_established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.restored_laws_model_established

/--
info: 'Tacenta.UnitLifecycleRestoredSession.restored_decrypt_hypotheses_jointly_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
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
 tacenta_session_unit.tacenta_kem.EncapsState.from_bytes,
 tacenta_session_unit.tacenta_kem.EncapsState.to_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.decapsulate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.ek_vector,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.from_bytes,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.generate,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.header,
 tacenta_session_unit.tacenta_kem.IncrementalKeyPair.to_bytes,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.TupleABC.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.as_slice,
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
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
 tacenta_session_unit.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
 tacenta_session_unit.lifecycle.PrekeyStore.to_bytes._native.decide.ax_1,
 tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes.Insts.CoreCmpPartialEqPublicKeyBytes.eq,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index,
 tacenta_session_unit.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.restored_decrypt_hypotheses_jointly_satisfiable

/--
info: 'Tacenta.UnitLifecycleRestoredSession.restored_decrypt_laws_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.rand_core_1.error.Error,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleRestoredSession.restored_decrypt_laws_model

/--
info: Tacenta.UnitLifecycleRestoredSession.import_ok_gives_invariant : ∀ (b : Aeneas.Std.Slice Aeneas.Std.U8)
  (s : tacenta_session_unit.lifecycle.Session),
  tacenta_session_unit.lifecycle.Session.import b = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) →
    s.invariant = Aeneas.Std.Result.ok true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.import_ok_gives_invariant

/--
info: Tacenta.UnitLifecycleRestoredSession.counterHeadroom_iff_check : ∀ (s : tacenta_session_unit.lifecycle.Session),
  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s ↔ Tacenta.UnitLifecycleRestoredSession.headroomCheck s = true
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.counterHeadroom_iff_check

/--
info: Tacenta.UnitLifecycleRestoredSession.sessionRefines_restored : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (K : Model.Braid.Kem) (s : tacenta_session_unit.lifecycle.Session),
  Tacenta.UnitLifecycleRestoredSession.RestoredScope s →
    Tacenta.UnitLifecycleT3.SessionRefines dh K s (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.sessionRefines_restored

/--
info: Tacenta.UnitLifecycleRestoredSession.sessionRefines_restored_unique : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (K : Model.Braid.Kem) (s : tacenta_session_unit.lifecycle.Session),
  Tacenta.UnitLifecycleRestoredSession.RestoredScope s →
    ∀ (m : Model.Lifecycle.Session),
      Tacenta.UnitLifecycleT3.SessionRefines dh K s m → m = Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.sessionRefines_restored_unique

/--
info: Tacenta.UnitLifecycleRestoredSession.honestChunk_restored : ∀ (dh : Tacenta.UnitLifecycleT3.DhView)
  (s : tacenta_session_unit.lifecycle.Session),
  Tacenta.UnitLifecycleRestoredSession.RestoredScope s →
    ∀ (msg : Model.Braid.Msg),
      Tacenta.SessionUnitBraidT3.HonestChunk (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s).braid msg
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.honestChunk_restored

/--
info: @Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.ofInvariant : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView}
  {oracle : Model.Lifecycle.Oracle} {bytes : Aeneas.Std.Slice Aeneas.Std.U8}
  {s : tacenta_session_unit.lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R},
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses rngCore cryptoRng trace dh view oracle bytes s message
      rng →
    Tacenta.UnitLifecycleDecryptRunBounds.DecryptOfInvariantHypotheses rngCore cryptoRng trace dh view oracle s
      (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s) message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.ofInvariant

/--
info: @Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.refines : ∀ {R : Type}
  {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
  {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView}
  {oracle : Model.Lifecycle.Oracle} {bytes : Aeneas.Std.Slice Aeneas.Std.U8}
  {s : tacenta_session_unit.lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R},
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses rngCore cryptoRng trace dh view oracle bytes s message
      rng →
    Tacenta.UnitLifecycleT3.PublicDecryptWitness rngCore cryptoRng trace dh oracle.braidKem view oracle s
      (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s) message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.refines

/--
info: @Tacenta.UnitLifecycleRestoredSession.restored_decrypt_refines : ∀ {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle),
  Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
    Tacenta.UnitLifecycleT3.DhCodecOf dh →
      Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
            ∀ (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (s : tacenta_session_unit.lifecycle.Session),
              tacenta_session_unit.lifecycle.Session.import bytes =
                  Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) →
                Tacenta.UnitLifecycleRestoredSession.RestoredScope s →
                  Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s →
                    ∀ (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
                      tacenta_session_unit.serialization.message_type message =
                          Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Ratchet) →
                        trace rng = oracle.draws →
                          (∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite)
                              (modelComposite : Model.CompositeHeader.Composite)
                              (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
                              Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
                                  Except.ok (modelComposite, ciphertext) →
                                Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
                                  Tacenta.UnitLifecycleT3.IncomingChunkRefines view
                                    (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s).braid realComposite
                                    modelComposite) →
                            (∃ draw rest, trace rng = draw :: rest) →
                              Tacenta.UnitLifecycleT3.PublicDecryptWitness rngCore cryptoRng trace dh oracle.braidKem
                                view oracle s (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s) message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.restored_decrypt_refines

/--
info: Tacenta.UnitLifecycleRestoredSession.model_kemCiphertextLenBound : Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape
  (Aeneas.Std.Result.ok 0#usize)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.model_kemCiphertextLenBound

/--
info: Tacenta.UnitLifecycleRestoredSession.codecShape_parts : Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
  Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
    Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
      ∀ {R : Type} {rc : tacenta_session_unit.rand_core_1.RngCore R}
        {crc : tacenta_session_unit.rand_core_1.CryptoRng R} {our : tacenta_session_unit.lifecycle.Identity}
        {bundle : tacenta_session_unit.lifecycle.PublishedBundle}
        (p : Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorOutputParts rc crc our bundle),
        Tacenta.UnitLifecycleSessionRoundTrip.CodecShape p.session 1#u64 p.auth 0#u64 { ck := p.sparseSend, n := 0#u64 }
          { ck := p.sparseReceive, n := 0#u64 }
          { ephemeral_public := p.ephemeralPublic, kem_ciphertext := p.kemCiphertext,
            signed_prekey_id := bundle.signed_prekey_id, one_time_prekey_id := bundle.one_time_prekey_id,
            kem_prekey_id := bundle.kem_prekey_id }
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.codecShape_parts

/--
info: Tacenta.UnitLifecycleRestoredSession.export_import_established : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
            Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
              Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ {E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore E)
                    (crc : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
                    (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                    (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                    (s : tacenta_session_unit.lifecycle.Session),
                    tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                      ∃ z v,
                        s.export = Aeneas.Std.Result.ok z ∧
                          tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                Tacenta.UnitLifecycleSessionCodec.vecInst z =
                              Aeneas.Std.Result.ok v ∧
                            tacenta_session_unit.lifecycle.Session.import v.deref =
                              Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.export_import_established

/--
info: Tacenta.UnitLifecycleRestoredSession.restored_established_continues : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
  Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
    Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
      Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
          Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
            Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
              Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                    @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                  ∀ {E : Type} (rc : tacenta_session_unit.rand_core_1.RngCore E)
                    (crc : tacenta_session_unit.rand_core_1.CryptoRng E) (our : tacenta_session_unit.lifecycle.Identity)
                    (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                    (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                    (s : tacenta_session_unit.lifecycle.Session),
                    tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected rng0 =
                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                      ∃ z v,
                        s.export = Aeneas.Std.Result.ok z ∧
                          tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                Tacenta.UnitLifecycleSessionCodec.vecInst z =
                              Aeneas.Std.Result.ok v ∧
                            tacenta_session_unit.lifecycle.Session.import v.deref =
                                Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) ∧
                              Tacenta.UnitLifecycleRestoredSession.RestoredScope s ∧
                                Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.restored_established_continues

/--
info: @Tacenta.UnitLifecycleRestoredSession.restored_established_initiator_decrypt_refines : ∀ {R E : Type},
  Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
    Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
      Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
        Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
          Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
              Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                  Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                      @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                    ∀ (rngCore : tacenta_session_unit.rand_core_1.RngCore R)
                      (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R) (trace : R → List Model.Lifecycle.Key)
                      (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
                      (oracle : Model.Lifecycle.Oracle),
                      Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle →
                        Tacenta.UnitLifecycleT3.DhCodecOf dh →
                          Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore →
                            ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
                              Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem →
                                ∀ (rc : tacenta_session_unit.rand_core_1.RngCore E)
                                  (crc : tacenta_session_unit.rand_core_1.CryptoRng E)
                                  (our : tacenta_session_unit.lifecycle.Identity)
                                  (bundle : tacenta_session_unit.lifecycle.PublishedBundle)
                                  (expected : tacenta_session_unit.tacenta_boundary.dh.PublicKeyBytes) (rng0 rng1 : E)
                                  (s : tacenta_session_unit.lifecycle.Session),
                                  tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle expected
                                        rng0 =
                                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) →
                                    ∀ (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R),
                                      tacenta_session_unit.serialization.message_type message =
                                          Aeneas.Std.Result.ok
                                            (some tacenta_session_unit.serialization.MessageType.Ratchet) →
                                        trace rng = oracle.draws →
                                          (∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite)
                                              (modelComposite : Model.CompositeHeader.Composite)
                                              (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
                                              Model.CompositeHeader.decodeDetailed
                                                    (Tacenta.UnitLifecycleT3.sliceOf message) =
                                                  Except.ok (modelComposite, ciphertext) →
                                                Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
                                                  Tacenta.UnitLifecycleT3.IncomingChunkRefines view
                                                    (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s).braid
                                                    realComposite modelComposite) →
                                            (∃ draw rest, trace rng = draw :: rest) →
                                              ∃ z v,
                                                s.export = Aeneas.Std.Result.ok z ∧
                                                  tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                                        Tacenta.UnitLifecycleSessionCodec.vecInst z =
                                                      Aeneas.Std.Result.ok v ∧
                                                    tacenta_session_unit.lifecycle.Session.import v.deref =
                                                        Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) ∧
                                                      Tacenta.UnitLifecycleT3.PublicDecryptWitness rngCore cryptoRng
                                                        trace dh oracle.braidKem view oracle s
                                                        (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s)
                                                        message rng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.restored_established_initiator_decrypt_refines

/--
info: @Tacenta.UnitLifecycleRestoredSession.restored_established_inhabited : ∀ {R : Type}
  (rc : tacenta_session_unit.rand_core_1.RngCore R) (crc : tacenta_session_unit.rand_core_1.CryptoRng R),
  Nonempty (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real rc) →
    Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real rc
        crc →
      Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
        Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
          Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
            Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
              Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
                  Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
                    Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                      Tacenta.UnitHeadroomInvariant.OptionEqU64Shape
                          @tacenta_session_unit.core.option.Option.Insts.CoreCmpPartialEqOption.eq →
                        ∀ (our : tacenta_session_unit.lifecycle.Identity) (rng0 : R),
                          ∃ bundle s rng1 z v,
                            tacenta_session_unit.lifecycle.establish_initiator_for rc crc our bundle
                                  bundle.bundle.identity_key rng0 =
                                Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s, rng1) ∧
                              s.export = Aeneas.Std.Result.ok z ∧
                                tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
                                      Tacenta.UnitLifecycleSessionCodec.vecInst z =
                                    Aeneas.Std.Result.ok v ∧
                                  tacenta_session_unit.lifecycle.Session.import v.deref =
                                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s) ∧
                                    Tacenta.UnitLifecycleRestoredSession.RestoredScope s ∧
                                      Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.restored_established_inhabited

/--
info: Tacenta.UnitLifecycleRestoredSession.restored_laws_model : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
    Tacenta.UnitSatisfiabilityJoint.Interp.model ∧
  Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape Tacenta.UnitSatisfiabilityJoint.Interp.model ∧
    Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape Tacenta.UnitSatisfiabilityJoint.Interp.model ∧
      Tacenta.UnitLifecycleSessionCodec.OptionBranchSomeShape @Tacenta.UnitLifecycleSessionCodec.optionBranchImpl ∧
        Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape @Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl ∧
          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape (Aeneas.Std.Result.ok 0#usize) ∧
            Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
                Tacenta.UnitSatisfiabilityJoint.Interp.model ∧
              Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (Aeneas.Std.Result.ok 0#usize)
                  Tacenta.UnitSatisfiabilityJoint.Interp.model ∧
                Tacenta.UnitHeadroomInvariant.OptionEqU64Shape @Tacenta.UnitHeadroomInvariant.optionEqImpl
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.restored_laws_model

/--
info: Tacenta.UnitLifecycleRestoredSession.restored_laws_model_established : Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
    Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
  Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape
      Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
    Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape
        Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      Tacenta.UnitLifecycleSessionCodec.OptionBranchSomeShape @Tacenta.UnitLifecycleSessionCodec.optionBranchImpl ∧
        Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape @Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl ∧
          Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape (Aeneas.Std.Result.ok 0#usize)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.restored_laws_model_established

/--
info: Tacenta.UnitLifecycleRestoredSession.restored_decrypt_hypotheses_jointly_satisfiable : ∀ (K : Model.Braid.Kem)
  (dh : Tacenta.UnitLifecycleT3.DhView),
  Tacenta.UnitLifecycleDecryptScreen.DecryptJointLaws K dh →
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) →
      Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape Tacenta.UnitSatisfiabilityJoint.Interp.real
          Tacenta.UnitLifecycleIntegrationScreen.byteRng Tacenta.UnitLifecycleIntegrationScreen.byteCrc →
        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValid →
          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenOf →
            Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTrip →
              Tacenta.UnitLifecycleSessionCodec.OptionBranchSome →
                Tacenta.UnitLifecycleSessionCodec.VecAsSlice →
                  Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTrip →
                    Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTrip →
                      Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound →
                        ∀ (our : tacenta_session_unit.lifecycle.Identity) (view : Model.Lifecycle.CodewordView),
                          ∃ oracle s v,
                            oracle.braidKem = K ∧
                              Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses
                                Tacenta.UnitLifecycleIntegrationScreen.byteRng
                                Tacenta.UnitLifecycleIntegrationScreen.byteCrc
                                Tacenta.UnitLifecycleIntegrationScreen.byteTrace dh view oracle v.deref s
                                Tacenta.UnitLifecycleDecryptRatchetScreen.sampleMessage
                                Tacenta.UnitLifecycleDecryptRatchetScreen.sampleRng
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.restored_decrypt_hypotheses_jointly_satisfiable

/--
info: Tacenta.UnitLifecycleRestoredSession.restored_decrypt_laws_model : (Tacenta.UnitLifecycleDecryptScreen.DecryptJointLawsShape
      Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished
      Tacenta.UnitLifecycleEstablishedDecrypt.viewEstablished Model.Braid.toyKem
      @Tacenta.UnitHeadroomInvariant.optionEqImpl ∧
    Nonempty
        (Tacenta.UnitSatisfiabilityJoint.InitiatorAxiom Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished
          Tacenta.UnitLifecycleIntegrationScreen.byteRng) ∧
      Tacenta.UnitLifecycleEstablishInitiatorShape.InitiatorSuccessShape
          Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished Tacenta.UnitLifecycleIntegrationScreen.byteRng
          Tacenta.UnitLifecycleIntegrationScreen.byteCrc ∧
        Tacenta.UnitLifecycleEstablishInitiatorShape.DhPublicValidShape
            Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
          Tacenta.UnitLifecycleEstablishInitiatorShape.KemCiphertextLenLawShape (Aeneas.Std.Result.ok 0#usize)
            Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished) ∧
  Tacenta.UnitLifecycleSessionCodec.ZeroizingVecRoundTripShape
      Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
    Tacenta.UnitLifecycleSessionCodec.DhPrivateBytesRoundTripShape
        Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
      Tacenta.UnitLifecycleSessionCodec.DhPublicBytesRoundTripShape
          Tacenta.UnitLifecycleEstablishedDecrypt.Interp.modelEstablished ∧
        Tacenta.UnitLifecycleSessionCodec.OptionBranchSomeShape @Tacenta.UnitLifecycleSessionCodec.optionBranchImpl ∧
          Tacenta.UnitLifecycleSessionCodec.VecAsSliceShape @Tacenta.UnitLifecycleSessionCodec.vecAsSliceImpl ∧
            Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape (Aeneas.Std.Result.ok 0#usize)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleRestoredSession.restored_decrypt_laws_model

/--
info: def Tacenta.UnitLifecycleRestoredSession.headroomCheck : tacenta_session_unit.lifecycle.Session → Bool :=
fun s =>
  (decide (↑s.triple.classical.events + 1 < Aeneas.Std.U32.max) &&
        decide (↑s.triple.post_quantum.epoch + 1 < Aeneas.Std.U64.max) &&
      (↑s.triple.post_quantum.chains).all fun p =>
        (match p.2.send with
          | some ch => decide (↑ch.n < Aeneas.Std.U64.max)
          | none => true) &&
          match p.2.receive with
          | some ch => decide (↑ch.n < Aeneas.Std.U64.max)
          | none => true) &&
    decide (↑(Tacenta.SessionUnitBraidT1.State.epoch_val s.braid.state) + 1 < Aeneas.Std.U64.max)
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredSession.headroomCheck

/--
info: def Tacenta.UnitLifecycleRestoredSession.RestoredScope : tacenta_session_unit.lifecycle.Session → Prop :=
fun s =>
  (∃ epoch auth, s.braid.state = tacenta_session_unit.tacenta_braid.State.KeysUnsampled epoch auth) ∨
    s.braid.state = tacenta_session_unit.tacenta_braid.State.Failed
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredSession.RestoredScope

/--
info: def Tacenta.UnitLifecycleRestoredSession.restoredModelOf : Tacenta.UnitLifecycleT3.DhView →
  tacenta_session_unit.lifecycle.Session → Model.Lifecycle.Session :=
fun dh s => Tacenta.UnitLifecycleEstablishInitiatorShape.establishedModelOf dh s
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredSession.restoredModelOf

/--
info: structure Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses {R : Type}
  (rngCore : tacenta_session_unit.rand_core_1.RngCore R) (cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R)
  (trace : R → List Model.Lifecycle.Key) (dh : Tacenta.UnitLifecycleT3.DhView) (view : Model.Lifecycle.CodewordView)
  (oracle : Model.Lifecycle.Oracle) (bytes : Aeneas.Std.Slice Aeneas.Std.U8)
  (s : tacenta_session_unit.lifecycle.Session) (message : Aeneas.Std.Slice Aeneas.Std.U8) (rng : R) : Prop
number of parameters: 11
fields:
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.accepted : tacenta_session_unit.lifecycle.Session.import
        bytes =
      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s)
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.scope : Tacenta.UnitLifecycleRestoredSession.RestoredScope
      s
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.counters : Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom
      s
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.oracleOf : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf
      rngCore cryptoRng dh trace oracle
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.codec : Tacenta.UnitLifecycleT3.DhCodecOf dh
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts
      rngCore
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.derivedKeys : Nonempty
      Tacenta.SessionUnitT1.DerivedKeysModel
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements
      oracle.braidKem
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.messageType : tacenta_session_unit.serialization.message_type
        message =
      Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Ratchet)
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.trace_eq : trace rng = oracle.draws
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.chunk : ∀
      (realComposite : tacenta_session_unit.tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
      (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
      Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
          Except.ok (modelComposite, ciphertext) →
        Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
          Tacenta.UnitLifecycleT3.IncomingChunkRefines view
            (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s).braid realComposite modelComposite
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.draw : ∃ draw rest, trace rng = draw :: rest
constructor:
  Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses.mk {R : Type}
    {rngCore : tacenta_session_unit.rand_core_1.RngCore R} {cryptoRng : tacenta_session_unit.rand_core_1.CryptoRng R}
    {trace : R → List Model.Lifecycle.Key} {dh : Tacenta.UnitLifecycleT3.DhView} {view : Model.Lifecycle.CodewordView}
    {oracle : Model.Lifecycle.Oracle} {bytes : Aeneas.Std.Slice Aeneas.Std.U8}
    {s : tacenta_session_unit.lifecycle.Session} {message : Aeneas.Std.Slice Aeneas.Std.U8} {rng : R}
    (accepted :
      tacenta_session_unit.lifecycle.Session.import bytes = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok s))
    (scope : Tacenta.UnitLifecycleRestoredSession.RestoredScope s)
    (counters : Tacenta.UnitLifecycleDecryptRunBounds.CounterHeadroom s)
    (oracleOf : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptOracleOf rngCore cryptoRng dh trace oracle)
    (codec : Tacenta.UnitLifecycleT3.DhCodecOf dh) (contracts : Tacenta.UnitLifecycleT1.DecryptRatchetContracts rngCore)
    (derivedKeys : Nonempty Tacenta.SessionUnitT1.DerivedKeysModel)
    (agreements : Tacenta.UnitLifecycleDecryptRatchetT3.DecryptRatchetAgreements oracle.braidKem)
    (messageType :
      tacenta_session_unit.serialization.message_type message =
        Aeneas.Std.Result.ok (some tacenta_session_unit.serialization.MessageType.Ratchet))
    (trace_eq : trace rng = oracle.draws)
    (chunk :
      ∀ (realComposite : tacenta_session_unit.tacenta_wire.Composite) (modelComposite : Model.CompositeHeader.Composite)
        (ciphertext : Tacenta.UnitLifecycleT3.Bytes),
        Model.CompositeHeader.decodeDetailed (Tacenta.UnitLifecycleT3.sliceOf message) =
            Except.ok (modelComposite, ciphertext) →
          Tacenta.UnitLifecycleT3.CompositeRefines realComposite modelComposite →
            Tacenta.UnitLifecycleT3.IncomingChunkRefines view
              (Tacenta.UnitLifecycleRestoredSession.restoredModelOf dh s).braid realComposite modelComposite)
    (draw : ∃ draw rest, trace rng = draw :: rest) :
    Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses rngCore cryptoRng trace dh view oracle bytes s
      message rng
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredSession.RestoredDecryptHypotheses

/--
info: def Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape : Aeneas.Std.Result Aeneas.Std.Usize → Prop :=
fun ciphertextLen => ∃ n, ciphertextLen = Aeneas.Std.Result.ok n ∧ ↑n ≤ 65536
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape

/--
info: def Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound : Prop :=
Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBoundShape tacenta_session_unit.tacenta_boundary.kem.ciphertext_len
-/
#guard_msgs in
#print Tacenta.UnitLifecycleRestoredSession.KemCiphertextLenBound
