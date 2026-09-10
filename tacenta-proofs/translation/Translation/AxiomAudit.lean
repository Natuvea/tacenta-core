import Model.AxiomAudit
import Translation
import Translation.SpqrT3
import Translation.BraidT3
import Translation.PreconditionWitness
import Translation.Satisfiability
import Translation.ImportInv
import Translation.ErasureWitness
import Translation.KemWitness

/-!
The translation package's axiom audit, over everything the root `Translation`
module imports plus the modules it cannot (`SpqrT3`, `BraidT3`,
`PreconditionWitness`, `Satisfiability`, `ErasureWitness`, `KemWitness`, which the `Translation.*`
glob builds on their own). `TripleT1`/`TripleT3` cannot be imported alongside
these -- `TacentaTriple` and `TacentaRatchet` both define
`instDiscriminantRatchetErrorIsize`, the same limit `lakefile.toml` records --
so they have their own audit in `Translation/AxiomAuditTriple.lean`.

`Model.AxiomAudit` refuses any first-party hand-written declaration that is
an axiom, opaque, unsafe or partial, or carries `implemented_by`/`extern`.
The generated `Translation.Tacenta*` modules are exempt from the axiom rule
only, since Aeneas declares every opaque external as an `axiom`;
`scripts/attest.py --check` holds those files to a recorded per-file axiom
set, so a new one fails there rather than being reclassified. Both `Model`
and `Translation` prefixes are audited here: the model is imported into this
package, and a widening in it would reach every refinement theorem.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Properties, `Proofs, `Translation]
