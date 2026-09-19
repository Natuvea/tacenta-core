import Model.AxiomAudit
import Translation.TacentaLifecycle

/-!
The Phase 0 lifecycle translation has its own axiom-audit environment. Aeneas
emits short global names for some dependency types, so importing this module
beside the separately generated leaf translations would create duplicate Lean
declarations. The package glob still builds this module and the lifecycle
translation on every run.

The generated module may declare opaque external calls. `attest.py` records
their exact names and compares this audit's environment view with that record;
every first-party hand-written declaration remains subject to the ordinary
no-axiom, no-opaque, no-unsafe and no-partial rule.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
