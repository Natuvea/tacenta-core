import Model.AxiomAudit
import Translation.SessionUnitT3
import Translation.SessionUnitSpqrT3
import Translation.SessionUnitSessionT1
import Translation.SessionUnitErasureT1

/-!
The eight-leaf Session translation unit's axiom audit. It is separate because
the unit re-declares the standalone leaf translations' generated names and
therefore cannot share their environment. The imported T1/T3 results cover the
classical and sparse ratchet leaves, the PQXDH derivation and the erasure coder in this namespace; no end-to-end Session
theorem is claimed here. Every generated declaration and opaque boundary is
visible to the same elaborated-environment audit used by the smaller units.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
