import Model.AxiomAudit
import Translation.TripleT1
import Translation.TripleT3

/-!
The Triple Ratchet half of the translation package's axiom audit. See
`Translation/AxiomAudit.lean` for the rule and for why the Triple modules
cannot share its import list: `tacenta-triple`'s own translation re-declares
the inner crates' instances under the same names as the standalone
translations, and Lean refuses to import both into one environment.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Translation]
