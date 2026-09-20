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

/-!
The eight-leaf Session translation unit's axiom audit. It is separate because
the unit re-declares the standalone leaf translations' generated names and
therefore cannot share their environment. The imported T1/T3 results cover
the classical and sparse ratchet leaves, all three decoded-state invariants,
the PQXDH derivation, the erasure coder and the Braid in this namespace. The
public lifecycle T1 roots and the session-invariant precondition bridge are
also audited here. The lifecycle T3 results are conditional branch lemmas:
each takes the leaf outcomes (`Braid::send`/`receive`, the Triple send or the
eviction receive, the model's twin of each) as hypotheses and relates one
step of the orchestration around them; they do not yet compose with the
unit's Braid and Triple refinements, and no lemma covers a successful
receive, the establishment paths or the public `decrypt` as a whole. Every
generated declaration and opaque boundary is visible to the
same elaborated-environment audit used by the smaller units.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
