import Model.AxiomAudit
import Translation.TripleT1
import Translation.TripleT3
import Translation.SatisfiabilityTriple

/-!
The Triple Ratchet half of the translation package's axiom audit. See
`Translation/AxiomAudit.lean` for the rule and for why the Triple modules
cannot share its import list: `tacenta-triple`'s own translation re-declares
the inner crates' instances under the same names as the standalone
translations, and Lean refuses to import both into one environment.
`Translation/SatisfiabilityTriple.lean`, the Triple half of the satisfiability
witnesses, is imported here for the same reason, so that its declarations
are walked too.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Translation]
