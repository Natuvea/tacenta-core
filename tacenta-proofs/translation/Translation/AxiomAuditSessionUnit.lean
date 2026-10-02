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
import Translation.UnitLifecycleT3
import Translation.UnitLifecycleInitialDispatch
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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_contracts

/-- info: 'Tacenta.UnitLifecycleT3.fullStoreOfReal_ne_of_generated_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleT3.fullStoreOfReal_ne_of_generated_ne

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
 Tacenta.SessionUnitSpqrT3.chain_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skip_val._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.max_skipped_store_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.protocol_info_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitSpqrT3.receive_refines_continuation._native.native_decide.ax_1_29,
 Tacenta.SessionUnitSpqrT3.root_label_agrees._native.native_decide.ax_1_1,
 Tacenta.SessionUnitTripleT3.combine_info_agrees._native.native_decide.ax_1_1,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
 tacenta_session_unit.zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
 tacenta_session_unit.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize,
 tacenta_session_unit.core.option.Option.Insts.CoreCloneClone.clone]
-/
#guard_msgs in
#print axioms Tacenta.UnitLifecycleT3.concrete_receive_attempt_store_full_from_retry_bounds

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
