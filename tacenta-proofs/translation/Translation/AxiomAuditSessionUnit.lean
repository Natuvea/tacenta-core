import Model.AxiomAudit
import Translation.SessionUnitT3
import Translation.SessionUnitSpqrT3
import Translation.SessionUnitSessionT1
import Translation.SessionUnitErasureT1
import Translation.SessionUnitBraidT1
import Translation.SessionUnitBraidT3
import Translation.SessionUnitRatchetImportInv
import Translation.SessionUnitBraidImportInv
import Translation.UnitSatisfiabilitySession
import Translation.SessionBraidReceiveVacuity
import Translation.SessionBraidReceiveRepair
import Translation.UnitSatisfiabilityErasure
import Translation.UnitSatisfiabilityRatchet
import Translation.UnitSatisfiabilityRecords
import Translation.UnitSatisfiabilityBraidAgreements
import Translation.UnitSatisfiabilityErasureAgrees
import Translation.UnitSatisfiabilityBraidStates
import Translation.UnitBraidEntryPoints
import Translation.UnitErasureRsDefs
import Translation.UnitErasureRsKernel
import Translation.UnitErasureRsAlgebra
import Translation.UnitErasureRsModel
import Translation.UnitErasureRsEncoder
import Translation.UnitErasureRsDecoder
import Translation.UnitErasureRsStatements
import Translation.UnitErasureRsGlue
import Translation.UnitSatisfiabilityZeroizeScope
import Translation.UnitLifecyclePublicT1
import Translation.UnitLifecycleReceivePreserve
import Translation.UnitLifecycleT3
import Translation.UnitLifecycleInitialDispatch
import Translation.UnitLifecycleInitiatorSecondMessage
import Translation.DispatchEvidenceVacuity
import Translation.SessionUnitBraidPreserveFacts
import Translation.UnitHeadroomSatisfiable
import Translation.UnitHeadroomInvariant
import Translation.NumericBoundarySession
import Translation.NumericWitnessSession
import Translation.SessionUnitDecodedStateDischarge
import Translation.SessionUnitBraidFromBytesWitness
import Translation.UnitLifecycleAtomicity
import Translation.UnitLifecycleRepair
import Translation.UnitLifecycleIntegrationScreen
import Translation.UnitOracleShape
import Translation.UnitOracleModel
import Translation.UnitOracleDh
import Translation.UnitOracleAead
import Translation.UnitOracleKemSig
import Translation.UnitOracleJoint
import Translation.UnitOracleDecrypt
import Translation.UnitLifecycleRetryLoopT3
import Translation.UnitLifecycleDecryptRatchetT3
import Translation.UnitLifecycleDecryptRatchetScreen
import Translation.UnitLifecycleTripleRefusalT3
import Translation.UnitLifecycleDecryptRatchetCompleteT3
import Translation.UnitLifecycleDecryptRatchetCompleteScreen
import Translation.UnitLifecycleDecryptScreen
import Translation.UnitLifecycleDecryptRunBounds
import Translation.UnitKemWrapperModel
import Translation.UnitHeldKemWitness
import Translation.SessionUnitDecodeEc
import Translation.UnitLifecycleDecryptStates
import Translation.UnitLifecycleInitialAgreementT3
import Translation.UnitLifecycleDecryptT3
import Translation.UnitLifecycleEstablishInitiatorShape
import Translation.UnitLifecycleEstablishedDecrypt
import Translation.UnitLifecycleSessionCodec
import Translation.UnitLifecycleSessionRoundTrip
import Translation.UnitLifecycleRestoredSession
import Translation.UnitLifecycleEstablishedEncrypt
import Translation.UnitLifecycleEstablishResponder
import Translation.UnitLifecycleResponderFirstFrame
import Translation.UnitLifecycleResponderFirstReceipt
import Translation.UnitLifecycleResponderSuccessor
import Translation.UnitLifecycleResponderReply
import Translation.UnitLifecycleResponderReplyReceipt
import Translation.UnitTripleInvModel
import Translation.UnitLifecycleSendPreserve
import Translation.UnitLifecycleInitiatorSecondSend

/-!
The eight-leaf Session translation unit's axiom audit. It is separate because
the unit re-declares the standalone leaf translations' generated names and
therefore cannot share their environment. The imported T1/T3 results cover
the classical and sparse ratchet leaves, all three decoded-state invariants,
the PQXDH derivation, the erasure coder and the Braid in this namespace. The
public lifecycle T1 roots and the session-invariant precondition bridge are
also audited here. The lifecycle T3 branch lemmas take leaf outcomes as
hypotheses. UnitLifecycleInitialDispatch composes the six initial-wrapper
routes, conditional on refinement of the inner ratchet receive, and discharges
that condition for terminal states and malformed payloads. Its T1 bridge
proves inner-call existence under explicit contracts and headroom. Those contracts included a
false field until it was restated for bounded decoders (`SessionBraidReceiveVacuity.lean`,
`SessionBraidReceiveRepair.lean`; `GAP-REGISTER.md`, row `SESSION-CONTRACT-VACUITY`).
`UnitSatisfiabilityRecords.lean` shows that the four records follow from an axiom base, over the
unit's opaque constants, that one interpretation satisfies (`UnitSatisfiabilityJoint.lean`); that
is an argument about derivations and not a statement that the real primitives meet the records.
`UnitOracleJoint.lean` and the five modules beneath it show that `OracleOf` is inhabited under
eleven laws, with a model; that is an argument about derivations and not a statement that the
real primitives meet the laws.
`UnitOracleDecrypt.lean` gives `DecryptOracleOf`, the four clauses the decrypt refinements take,
from four of those laws, without the KEM and signing laws.
`UnitLifecycleDecryptScreen.lean` shows the hypotheses of the complete `decrypt_ratchet` refinement,
with `Session::invariant`, together at one witness under named laws that one interpretation satisfies,
the agreements at the same oracle's KEM model; the witness state is built for the hypotheses.
`UnitLifecycleDecryptRunBounds.lean` derives that refinement's per-run receive bounds from
`Session::invariant` and four counter ceilings, which stay assumed, and restates it with them.
`UnitLifecycleEstablishInitiatorShape.lean` derives, at every successful `establish_initiator_for`
output, `Session::invariant` (under two assumed laws about X25519 public keys and the KEM ciphertext
length, with models) and the four counter ceilings, with no hypothesis for the ceilings, and the relation
to the model session read off the output, which holds by definition at its `KeysUnsampled` Braid; `UnitLifecycleEstablishedDecrypt.lean` feeds them to the
`decrypt_ratchet` refinement and, for ratchet-type frames, to the public `decrypt`.
`UnitLifecycleRestoredSession.lean` shows every session `Session::import` accepts passes
`Session::invariant` (no hypothesis), relates an accepted session whose Braid is `KeysUnsampled` or `Failed`
to the model session read off it (by definition) and composes it with `decrypt` under the caller's boundary
records, chunk relation and draw; with `UnitLifecycleSessionCodec.lean` and
`UnitLifecycleSessionRoundTrip.lean` it proves that `import` of `export` returns every established initiator
session unchanged, under nine assumed laws, which hold with the decrypt laws in one interpretation.
`UnitLifecycleEstablishedEncrypt.lean` composes the public `encrypt` with every successful
`establish_initiator_for` output, under the encrypt boundary records, the oracle record and three assumed laws
(that key generation reads the two draws the model counts, `KeyGenSeededFor`, and `KemCiphertextLenOf` and
`KemCiphertextLenBound`); it names the two outcomes (key generation refusing,
or the initial message wrapping the first ratchet frame) with their effects and draws, and derives, after a
success, `Session::invariant`, the four counter ceilings and the relation to the model's next session under
the establishment's laws, two KEM agreements, `DivCeilValue` and an assumed size law of the model KEM; the
premise lists hold together with the decrypt, establishment and restored-session laws in one interpretation.
`UnitLifecycleEstablishResponder.lean` composes the public `establish_responder` for every input (each
return is a refusal before the inner receive with the store and the source of randomness as given, an inner
refusal with the store as given, or an inner success with the named store commit), derives
`Session::invariant`, the four ceilings and the relation for the session it builds, and applies the
`decrypt_ratchet` refinement to its inner call; that module exhibits no input at which the whole call succeeds.
`UnitLifecycleResponderFirstFrame.lean` feeds the bytes a successful first `encrypt` at an
`establish_initiator_for` output returns to `establish_responder`, at a store whose `publish` returned the bundle
the initiator used: under a DH symmetry law, a per-run KEM premise and the store's distinct identifiers (named),
the call refuses only with the three refusals the store decides, on the last-resort path, or reaches the inner
receive with the initiator's shared secret, where the invariant, the ceilings and the relation hold; the laws
hold in one interpretation and one run reaches the inner receive; that module does not show the inner receive succeeding.
`UnitLifecycleResponderFirstReceipt.lean` continues on the same bytes: past the store's refusals the inner receive
returns exactly one of a non-contributory candidate agreement, an AEAD refusal (store as given, one draw each) or
what the open of the initiator's seal returns; under two further boundary laws (the AEAD opens what it sealed, and
an agreement with a key `public_key` returned is not refused) and a per-run draw premise, the inner receive returns
the initiator's plaintext and the whole call succeeds with the committed store and one draw, its session related
to the model's step at a view that attributes the received chunk to the initiator's header source; the laws hold
in one interpretation and one run reaches the success.  A tampered frame being refused is not shown.
`UnitLifecycleResponderSuccessor.lean` shows, at the session that successful call returns, that `Session::invariant`
returns `true` and the four counter ceilings hold, for this first receive only: the receive's success walk, the
relation's fixing of the Triple and the agreement's state, and a walk of the agreement's receive for its decoder; no
law is added, and the reach run's responder session meets both.
`UnitLifecycleResponderReply.lean` takes the responder's `Session::encrypt` at that same session, on the same run: it
returns the bare reply frame (agreement type `none`, no chunk, no initial wrapper) sealed under the key of the
receipt's sending chain and the sparse chain the initiator receives on, takes no draw, keeps the agreement, and
relates to the model's step; the receipt's root-key and agreement equations and the equal associated data are kept
on that route.  No law is added; one reach run's responder encrypts after the receipt.
`UnitLifecycleResponderReplyReceipt.lean` takes those bytes to the initiator, on the same run: its public
`Session::decrypt` at the session its first `encrypt` left is analysed into the four arms of the model's step, of which
the theorem's own premises (contributory agreement, AEAD round trip) exclude two: it refuses `NoReceivingChain` exactly
when the reply's ratchet key is the peer key it already holds, and otherwise returns the responder's plaintext, takes
one draw, clears the pending initial message and relates to the model's step.  The laws are the receipt's, with the roles swapped; a new joint model
with a public key that varies holds them all, and the reach's law `DhPublicNotConstant` with them.  One reach run's
initiator receives the reply, and another, whose responder draws its own signed prekey secret, refuses it.
`UnitTripleInvModel.lean` states `Triple::invariant` on the model: at every code Triple that refines a model Triple,
the invariant returns `true` exactly when the model predicate `ModelTripleInv` holds, in both directions, from the
leaves' `Inv` and the canonicity transport; kernel only.  `UnitLifecycleSendPreserve.lean` proves that a successful
`Session::encrypt` at an agreement state whose send takes no draw keeps `Session::invariant` and spends one unit of a
counter budget whose zero is the four ceilings, given the relation after the call, under `KemCloneAgrees` only and
resting on the kernel and opaque constants; on the run it gives the invariant and the ceilings at the session the
responder's reply leaves, under the reply's hypotheses.  Draw states, an agreement output, refusals and receives are
not covered.
`UnitLifecycleInitiatorSecondSend.lean` takes the initiator's next `Session::encrypt` at the session that receipt
returns, on the same run: the model's step there has one outcome (the bare second frame, agreement type `hdr` with the
header's chunk at index 1, no draw), and if that session passes `Session::invariant` and meets the four counter ceilings,
which is not shown, the call returns those bytes, leaves the source as given and relates to the model's step.  The
encrypt route's providers come from the invariant and the ceilings, for every session whose agreement send reads no
draw.  No law is added, and no run is exhibited at which the invariant and the ceilings hold there.
`UnitLifecycleReceivePreserve.lean` states one receive step for every invariant session: a successful
`decrypt_ratchet` or `decrypt` whose model step is an in-order receive (no stored key, no skip, no agreement
output) leaving the agreement at `NoHeaderReceived` (at most one chunk held) or `KeysSampled` keeps
`Session::invariant` and spends one unit of the counter budget, given the relation after the call, under
`KemCloneAgrees`, the oracle's `dhPublic` clause, the view's codec and `DhPublicValid`; no law is added.  On the
runs it gives the invariant and the four ceilings at the session the initiator's receipt of the reply returns,
and re-derives them at the session the responder's receipt of the first frame returns.  A receive outside that
scope and a refused call are not covered; the join with the initiator's second send is the next module's.
`UnitLifecycleInitiatorSecondMessage.lean` joins the initiator's second `encrypt` with that receive step on one
run: under the hypotheses of the receipt of the reply and a bound on the second plaintext, with no new law, the
session the receipt returns passes `Session::invariant` and meets the four ceilings, the second `encrypt` there
returns the bare second frame with no draw and refines the model's step, and the session it leaves passes the
invariant and meets the ceilings; a reach exhibits such a run at the real constants under assumed laws.  The
responder's receipt of that message and every later step are not covered.
`UnitKemWrapperModel.lean` builds that KEM model from the `tacenta_kem` wrapper's opaque functions
read through byte views and proves the KEM agreements of it from eight laws about those functions,
with a model; that is not a statement that the real wrapper meets the laws.
`UnitHeldKemWitness.lean` shows the same hypotheses together at a second witness whose Braid holds a
generated key pair, so that the relation compares that KEM model's values with the real key pair's; that
witness state is built for the hypotheses too.
`UnitLifecycleDecryptStates.lean` builds sessions that pass `Session::invariant` with an established
ephemeral key, with a pending initial message, and with stored keys, open chains and counters away from
zero, and shows the hypotheses of the restated refinement together at the last; those states are built for
the hypotheses too, not shown produced by establishment or `import`.
`SessionUnitDecodeEc.lean` states the translated `decode_ec` on every input, refusals included, as
the model's `DecodeEC`. `UnitLifecycleInitialAgreementT3.lean` proves the repeated-initial
ephemeral comparison of `Session::decrypt` refines the model's, under the agreement clause of the
oracle and `DhCodecOf`; the initial-frame composition of `decrypt` is not there.
`DispatchEvidenceVacuity.lean` shows five evidence hypotheses and records of the lifecycle and
initial-dispatch modules to be false or empty (`GAP-REGISTER.md`, row `DISPATCH-EVIDENCE-VACUITY`). General
receive refinement and the full public Session T3 theorem remain open. Every
is an argument about derivations and not a statement that the real primitives meet the records. General
receive refinement and the full public Session T3 theorem remain open. The
numeric-precondition modules of the unit (`NumericBoundarySession`,
`NumericWitnessSession` and `SessionUnitDecodedStateDischarge`) are walked here
as well. Every
generated declaration and opaque boundary is visible to the
same elaborated-environment audit used by the smaller units.
-/

/--
info: 'Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_contracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_contracts

/--
info: Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_contracts : Tacenta.SessionUnitT3.HmacAgrees →
  Tacenta.SessionUnitT3.HkdfAgrees →
    Tacenta.SessionUnitT3.ZeroizingRoundTrips →
      Tacenta.SessionUnitT1.RemoveSkippedAtTotal →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
                Tacenta.SessionUnitSpqrT1.VecRetainTotal →
                  Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
                    Tacenta.SessionUnitSpqrT1.ZeroizeTotal →
                      Tacenta.SessionUnitSpqrT1.OptionCloneTotal →
                        ∀ {s : tacenta_session_unit.tacenta_triple.State} {m : Model.Triple.State},
                          Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
                              Tacenta.SessionUnitTripleT3.spqrAbs s m →
                            ∀ (header : tacenta_session_unit.tacenta_triple.Header) (mh : Model.State.Header),
                              Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr mh →
                                ∀ (dh_out_recv dh_out_send new_dhs_pub : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
                                  (output : Option tacenta_session_unit.tacenta_spqr.Output),
                                  (List.filter (fun x => x.1 == mh.dh && x.2.1 == mh.n) m.classical.skipped).length ≤
                                      1 →
                                    max m.classical.skipped.length Model.State.maxSkippedStore + Model.State.maxSkip ≤
                                        Aeneas.Std.Usize.max →
                                      m.classical.events + 1 < Aeneas.Std.U32.max →
                                        m.postQuantum.epoch + 1 < Aeneas.Std.U64.max →
                                          m.postQuantum.chains.length + 2 < Aeneas.Std.Usize.max →
                                            (∀ p ∈ m.postQuantum.chains,
                                                p.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max) →
                                              (∀ sk ∈ m.postQuantum.skipped,
                                                  sk.1 + Model.SparseRatchet.epochsKept ≤ Aeneas.Std.U64.max) →
                                                (∀ (o : tacenta_session_unit.tacenta_spqr.Output),
                                                    output = some o →
                                                      ↑o.key_epoch + Model.SparseRatchet.epochsKept ≤
                                                        Aeneas.Std.U64.max) →
                                                  m.postQuantum.skipped.length + Model.SparseRatchet.maxSkip ≤
                                                      Aeneas.Std.Usize.max →
                                                    (List.filter
                                                            (fun x => x.1 == ↑header.epoch && x.2.1 == ↑header.pq_n)
                                                            m.postQuantum.skipped).length ≤
                                                        1 →
                                                      (∀ p ∈ m.postQuantum.chains,
                                                          ∀ (ch : Model.SparseRatchet.Chain),
                                                            p.2.send = some ch ∨ p.2.receive = some ch →
                                                              ch.n < Aeneas.Std.U64.max) →
                                                        ∀ (realReason : tacenta_session_unit.tacenta_triple.TripleError)
                                                          (half : tacenta_session_unit.lifecycle.FullStore),
                                                          tacenta_session_unit.lifecycle.receive_attempt s header
                                                                dh_out_recv dh_out_send new_dhs_pub output =
                                                              Aeneas.Std.Result.ok
                                                                (Aeneas.Std.core.result.Result.Err realReason) →
                                                            tacenta_session_unit.lifecycle.full_store realReason =
                                                                Aeneas.Std.Result.ok (some half) →
                                                              ∃ modelReason,
                                                                Model.Triple.receiveDetailed m
                                                                      { dr := mh, epoch := ↑header.epoch,
                                                                        pqN := ↑header.pq_n }
                                                                      (Tacenta.SessionUnitTripleT3.keyOf dh_out_recv)
                                                                      (Tacenta.SessionUnitTripleT3.keyOf dh_out_send)
                                                                      (Tacenta.SessionUnitTripleT3.keyOf new_dhs_pub)
                                                                      (Option.map
                                                                        Tacenta.SessionUnitTripleT3.spqrOutputOf
                                                                        output) =
                                                                    Except.error modelReason ∧
                                                                  Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal
                                                                        realReason =
                                                                      some modelReason ∧
                                                                    Model.Lifecycle.fullStore modelReason =
                                                                      some
                                                                        (Tacenta.UnitLifecycleT3.fullStoreOfReal half)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_contracts

/-- info: 'Tacenta.UnitLifecycleT3.fullStoreOfReal_ne_of_generated_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleT3.fullStoreOfReal_ne_of_generated_ne

/--
info: @Tacenta.UnitLifecycleT3.fullStoreOfReal_ne_of_generated_ne : ∀ {left right : tacenta_session_unit.lifecycle.FullStore},
  Aeneas.Std.core.cmp.PartialEq.ne.trait_default
        tacenta_session_unit.lifecycle.FullStore.Insts.CoreCmpPartialEqFullStore left right =
      Aeneas.Std.Result.ok true →
    Tacenta.UnitLifecycleT3.fullStoreOfReal left ≠ Tacenta.UnitLifecycleT3.fullStoreOfReal right
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleT3.fullStoreOfReal_ne_of_generated_ne

/--
info: 'Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_retry_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.tacenta_kdf.hmac_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_retry_bounds

/--
info: Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_retry_bounds : Tacenta.SessionUnitT3.HmacAgrees →
  Tacenta.SessionUnitT3.HkdfAgrees →
    Tacenta.SessionUnitT3.ZeroizingRoundTrips →
      Tacenta.SessionUnitT1.RemoveSkippedAtTotal →
        ∀ [Tacenta.SessionUnitT1.DerivedKeysModel],
          Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips96 →
            Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
              Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
                Tacenta.SessionUnitSpqrT1.VecRetainTotal →
                  Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
                    Tacenta.SessionUnitSpqrT1.ZeroizeTotal →
                      Tacenta.SessionUnitSpqrT1.OptionCloneTotal →
                        ∀ {state : tacenta_session_unit.tacenta_triple.State} {modelState : Model.Triple.State},
                          Tacenta.SessionUnitTripleT3.StateRefines Tacenta.SessionUnitTripleT3.ratchetAbs
                              Tacenta.SessionUnitTripleT3.spqrAbs state modelState →
                            ∀ (header : tacenta_session_unit.tacenta_triple.Header) (modelHeader : Model.State.Header),
                              Tacenta.SessionUnitTripleT3.RatchetHeaderR header.dr modelHeader →
                                ∀ (dhOutRecv dhOutSend newDhsPub : Aeneas.Std.Array Aeneas.Std.U8 32#usize)
                                  (output : Option tacenta_session_unit.tacenta_spqr.Output),
                                  Tacenta.UnitLifecycleT3.RetryReceiveBounds modelState header modelHeader output →
                                    ∀ (realReason : tacenta_session_unit.tacenta_triple.TripleError)
                                      (half : tacenta_session_unit.lifecycle.FullStore),
                                      tacenta_session_unit.lifecycle.receive_attempt state header dhOutRecv dhOutSend
                                            newDhsPub output =
                                          Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err realReason) →
                                        tacenta_session_unit.lifecycle.full_store realReason =
                                            Aeneas.Std.Result.ok (some half) →
                                          ∃ modelReason,
                                            Model.Triple.receiveDetailed modelState
                                                  { dr := modelHeader, epoch := ↑header.epoch, pqN := ↑header.pq_n }
                                                  (Tacenta.SessionUnitTripleT3.keyOf dhOutRecv)
                                                  (Tacenta.SessionUnitTripleT3.keyOf dhOutSend)
                                                  (Tacenta.SessionUnitTripleT3.keyOf newDhsPub)
                                                  (Option.map Tacenta.SessionUnitTripleT3.spqrOutputOf output) =
                                                Except.error modelReason ∧
                                              Tacenta.UnitLifecycleT3.tripleReceiveRefusalOfReal realReason =
                                                  some modelReason ∧
                                                Model.Lifecycle.fullStore modelReason =
                                                  some (Tacenta.UnitLifecycleT3.fullStoreOfReal half)
-/
#guard_msgs in
#check @Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_retry_bounds


/-!
The constants of the Session unit's sparse ratchet and Triple refinements that the lifecycle results
inherit: the four label byte strings, the two skip bounds and `MAX_SKIP`'s value, the fact that
`(1 : u64)` has value one inside `receive_refines_continuation`, and the Triple's combine label (with its
split label and `split_secret_refines`, which no lifecycle result reaches).  Each was decided by
`native_decide` until 2026-10-21, which put a compiler-trust axiom under every lifecycle result through
them; each is now proved by `simp`, `decide` and `rfl`, so its pin names the kernel's three axioms, and
the two refinements' pins name those and the opaque externals only.
-/

/--
info: 'Tacenta.SessionUnitSpqrT3.protocol_info_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitSpqrT3.protocol_info_agrees

/--
info: Tacenta.SessionUnitSpqrT3.protocol_info_agrees : Tacenta.SessionUnitSpqrT3.sliceOf
    tacenta_session_unit.tacenta_spqr.PROTOCOL_INFO =
  Model.SparseRatchet.protocolInfo
-/
#guard_msgs in
#check @Tacenta.SessionUnitSpqrT3.protocol_info_agrees

/--
info: 'Tacenta.SessionUnitSpqrT3.chain_start_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitSpqrT3.chain_start_agrees

/--
info: Tacenta.SessionUnitSpqrT3.chain_start_agrees : Tacenta.SessionUnitSpqrT3.sliceOf
    tacenta_session_unit.tacenta_spqr.CHAIN_START_LABEL =
  Model.SparseRatchet.chainStart
-/
#guard_msgs in
#check @Tacenta.SessionUnitSpqrT3.chain_start_agrees

/--
info: 'Tacenta.SessionUnitSpqrT3.root_label_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitSpqrT3.root_label_agrees

/--
info: Tacenta.SessionUnitSpqrT3.root_label_agrees : Tacenta.SessionUnitSpqrT3.sliceOf
    tacenta_session_unit.tacenta_spqr.ROOT_LABEL =
  Model.SparseRatchet.rootLabel
-/
#guard_msgs in
#check @Tacenta.SessionUnitSpqrT3.root_label_agrees

/--
info: 'Tacenta.SessionUnitSpqrT3.chain_label_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitSpqrT3.chain_label_agrees

/--
info: Tacenta.SessionUnitSpqrT3.chain_label_agrees : Tacenta.SessionUnitSpqrT3.sliceOf
    tacenta_session_unit.tacenta_spqr.CHAIN_LABEL =
  Model.SparseRatchet.chainLabel
-/
#guard_msgs in
#check @Tacenta.SessionUnitSpqrT3.chain_label_agrees

/--
info: 'Tacenta.SessionUnitSpqrT3.max_skip_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitSpqrT3.max_skip_agrees

/--
info: Tacenta.SessionUnitSpqrT3.max_skip_agrees : ↑tacenta_session_unit.tacenta_spqr.MAX_SKIP = Model.SparseRatchet.maxSkip
-/
#guard_msgs in
#check @Tacenta.SessionUnitSpqrT3.max_skip_agrees

/--
info: 'Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees

/--
info: Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees : ↑tacenta_session_unit.tacenta_spqr.MAX_SKIPPED_STORE =
  Model.SparseRatchet.maxSkippedStore
-/
#guard_msgs in
#check @Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees

/--
info: 'Tacenta.SessionUnitSpqrT3.max_skip_val' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitSpqrT3.max_skip_val

/--
info: Tacenta.SessionUnitSpqrT3.max_skip_val : ↑tacenta_session_unit.tacenta_spqr.MAX_SKIP = 1000
-/
#guard_msgs in
#check @Tacenta.SessionUnitSpqrT3.max_skip_val

/--
info: 'Tacenta.SessionUnitSpqrT3.receive_refines_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 tacenta_session_unit.tacenta_kdf.hkdf_sha256,
 tacenta_session_unit.zeroize.Zeroizing,
 tacenta_session_unit.zeroize.Zeroizing.new,
 tacenta_session_unit.Array.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.Pair.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.alloc.vec.Vec.capacity,
 tacenta_session_unit.alloc.vec.Vec.pop,
 tacenta_session_unit.core.option.Option.as_mut,
 tacenta_session_unit.zeroize.Zeroize.Blanket.zeroize,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitSpqrT3.receive_refines_continuation

/--
info: Tacenta.SessionUnitSpqrT3.receive_refines_continuation : Tacenta.SessionUnitSpqrT3.SpqrHkdfAgrees →
  Tacenta.SessionUnitSpqrT3.ZeroizingRoundTrips64 →
    Tacenta.SessionUnitSpqrT3.VecRetainAgrees →
      Tacenta.SessionUnitSpqrT1.VecRetainTotal →
        Tacenta.SessionUnitSpqrT3.RemoveSkippedAtAgrees →
          Tacenta.SessionUnitSpqrT1.ZeroizeTotal →
            Tacenta.SessionUnitSpqrT1.OptionCloneTotal →
              ∀ {self1 : tacenta_session_unit.tacenta_spqr.State} {m1 : Model.SparseRatchet.State},
                Tacenta.SessionUnitSpqrT3.StateRefines self1 m1 →
                  ∀ (receiving_epoch n : Aeneas.Std.U64),
                    (↑self1.chains).length + 1 < Aeneas.Std.Usize.max →
                      (↑self1.skipped).length + ↑tacenta_session_unit.tacenta_spqr.MAX_SKIP ≤ Aeneas.Std.Usize.max →
                        (List.filter (fun x => x.1 == ↑receiving_epoch && x.2.1 == ↑n) m1.skipped).length ≤ 1 →
                          Tacenta.SessionUnitSpqrT3.ChainCounterBounded m1.chains →
                            Aeneas.Std.WP.spec
                              (do
                                let (o, self2) ← self1.try_skipped receiving_epoch n
                                match o with
                                  | none => do
                                    let i ← Aeneas.Std.lift (Aeneas.Std.core.num.U64.saturating_sub n 1#u64)
                                    let (r1, self3) ← self2.skip_message_keys receiving_epoch i
                                    let cf1 ← Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch r1
                                    match cf1 with
                                      | Aeneas.Std.core.ops.control_flow.ControlFlow.Continue a => do
                                        let o1 ← self3.find_chains receiving_epoch
                                        match o1 with
                                          | none =>
                                            Aeneas.Std.Result.ok
                                              (Aeneas.Std.core.result.Result.Err
                                                  tacenta_session_unit.tacenta_spqr.SpqrError.NoChain,
                                                self3)
                                          | some cs => do
                                            let cs1 ←
                                              tacenta_session_unit.tacenta_spqr.Chains.Insts.CoreCloneClone.clone cs
                                            match cs1.receive with
                                              | none =>
                                                Aeneas.Std.Result.ok
                                                  (Aeneas.Std.core.result.Result.Err
                                                      tacenta_session_unit.tacenta_spqr.SpqrError.ChainRetired,
                                                    self3)
                                              | some ch => do
                                                let ch1 ←
                                                  tacenta_session_unit.tacenta_spqr.Chain.Insts.CoreCloneClone.clone ch
                                                let o2 ← Aeneas.Std.lift (ch1.n.checked_add 1#u64)
                                                match o2 with
                                                  | none =>
                                                    Aeneas.Std.Result.ok
                                                      (Aeneas.Std.core.result.Result.Err
                                                          tacenta_session_unit.tacenta_spqr.SpqrError.ChainExhausted,
                                                        self3)
                                                  | some expected =>
                                                    if (n != expected) = true then
                                                      Aeneas.Std.Result.ok
                                                        (Aeneas.Std.core.result.Result.Err
                                                            tacenta_session_unit.tacenta_spqr.SpqrError.OutOfOrder,
                                                          self3)
                                                    else do
                                                      let (next, mk) ← tacenta_session_unit.tacenta_spqr.kdf_ck ch1.ck n
                                                      let o3 ←
                                                        tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone
                                                            tacenta_session_unit.tacenta_spqr.Chain.Insts.CoreCloneClone
                                                            cs1.send
                                                      let self4 ←
                                                        self3.set_chains receiving_epoch
                                                            { send := o3, receive := some { ck := next, n := n } }
                                                      Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok mk, self4)
                                      | Aeneas.Std.core.ops.control_flow.ControlFlow.Break residual => do
                                        let r2 ←
                                          Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              (Aeneas.Std.Array Aeneas.Std.U8 32#usize)
                                              (Aeneas.Std.core.convert.FromSame
                                                tacenta_session_unit.tacenta_spqr.SpqrError)
                                              residual
                                        Aeneas.Std.Result.ok (r2, self3)
                                  | some k => Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok k, self2))
                              fun r =>
                              (match
                                  match Model.SparseRatchet.trySkipped m1 ↑receiving_epoch ↑n with
                                  | some res => some res
                                  | none =>
                                    match Model.SparseRatchet.skipMessageKeys m1 (↑receiving_epoch) (↑n - 1) with
                                    | none => none
                                    | some st2 =>
                                      match Model.SparseRatchet.findChains st2 ↑receiving_epoch with
                                      | none => none
                                      | some cs =>
                                        match cs.receive with
                                        | none => none
                                        | some ch =>
                                          if ch.n < Model.SparseRatchet.u64Max then
                                            if ↑n = ch.n + 1 then
                                              some
                                                (Model.SparseRatchet.setChains st2 ↑receiving_epoch
                                                    { send := cs.send,
                                                      receive :=
                                                        some
                                                          { ck := (Model.SparseRatchet.kdfCk ch.ck ↑n).1, n := ↑n } },
                                                  (Model.SparseRatchet.kdfCk ch.ck ↑n).2)
                                            else none
                                          else none with
                                | none => ∃ err, r.1 = Aeneas.Std.core.result.Result.Err err
                                | some (m', k) =>
                                  ∃ key,
                                    r.1 = Aeneas.Std.core.result.Result.Ok key ∧
                                      Tacenta.SessionUnitSpqrT3.keyOf key = k ∧
                                        Tacenta.SessionUnitSpqrT3.StateRefines r.2 m') ∧
                                (r.1 =
                                    Aeneas.Std.core.result.Result.Err
                                      tacenta_session_unit.tacenta_spqr.SpqrError.SkippedStoreFull →
                                  Model.SparseRatchet.receiveDetailed m1 (↑receiving_epoch) none ↑n =
                                    Except.error Model.SparseRatchet.ReceiveRefusal.skippedStoreFull)
-/
#guard_msgs in
#check @Tacenta.SessionUnitSpqrT3.receive_refines_continuation

/--
info: 'Tacenta.SessionUnitTripleT3.combine_info_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitTripleT3.combine_info_agrees

/--
info: Tacenta.SessionUnitTripleT3.combine_info_agrees : Tacenta.SessionUnitTripleT3.sliceOf
    tacenta_session_unit.tacenta_triple.COMBINE_INFO =
  Model.TripleRatchet.combineInfo
-/
#guard_msgs in
#check @Tacenta.SessionUnitTripleT3.combine_info_agrees

/--
info: 'Tacenta.SessionUnitTripleT3.split_info_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tacenta.SessionUnitTripleT3.split_info_agrees

/--
info: Tacenta.SessionUnitTripleT3.split_info_agrees : Tacenta.SessionUnitTripleT3.sliceOf
    tacenta_session_unit.tacenta_triple.SPLIT_INFO =
  Model.TripleRatchet.splitInfo
-/
#guard_msgs in
#check @Tacenta.SessionUnitTripleT3.split_info_agrees

/--
info: 'Tacenta.SessionUnitTripleT3.split_secret_refines' depends on axioms: [propext,
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
#print axioms Tacenta.SessionUnitTripleT3.split_secret_refines

/--
info: Tacenta.SessionUnitTripleT3.split_secret_refines : Tacenta.SessionUnitTripleT3.TripleHkdfAgrees →
  Tacenta.SessionUnitTripleT3.ZeroizingRoundTrips →
    ∀ (sk : Aeneas.Std.Slice Aeneas.Std.U8),
      Aeneas.Std.WP.spec (tacenta_session_unit.tacenta_triple.split_secret sk) fun r =>
        (Tacenta.SessionUnitTripleT3.keyOf r.1, Tacenta.SessionUnitTripleT3.keyOf r.2) =
          Model.TripleRatchet.splitSecret (Tacenta.SessionUnitTripleT3.sliceOf sk)
-/
#guard_msgs in
#check @Tacenta.SessionUnitTripleT3.split_secret_refines

run_cmd _root_.Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
