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
import Translation.UnitLifecyclePublicT1
import Translation.UnitLifecycleT3
import Translation.UnitLifecycleInitialDispatch

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
proves inner-call existence under explicit contracts and headroom. General
receive refinement and the full public Session T3 theorem remain open. Every
generated declaration and opaque boundary is visible to the
same elaborated-environment audit used by the smaller units.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
