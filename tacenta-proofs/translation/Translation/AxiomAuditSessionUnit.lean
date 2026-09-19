import Model.AxiomAudit
import Translation.TacentaSessionUnit

/-!
The eight-leaf Session translation unit's axiom audit. It is separate because
the unit re-declares the standalone leaf translations' generated names and
therefore cannot share their environment. No Session theorem is claimed here;
this first commit makes every generated declaration and opaque boundary visible
to the same elaborated-environment audit used by the smaller units.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
