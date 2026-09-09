import Model.AxiomAudit
import Proofs.ErrorHandling
import Proofs.KeyErasure
import Proofs.MemorySafety
import Proofs.RatchetCorrectness
import Proofs.Serialization
import Proofs.SessionEstablishment
import Proofs.SparseRatchetCorrectness
import Proofs.StateInvariants
import Proofs.TrustedBase

/-!
The proofs package's axiom audit: every `Proofs.*` module, and through them
the `Model.*` modules they import, walked by `Model.AxiomAudit`. The `Proofs`
library's glob builds every submodule, so `lake build` here, `scripts/verify.sh`
and the incomplete-declaration scan's second build all run it (that script's
name cannot appear here: `verify.sh` greps this directory for the word it is
named after). A new module under `Proofs/` must be added to the imports above
to be audited.
-/

run_cmd Model.AxiomAudit.run #[`Model, `Proofs]
