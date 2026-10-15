import Lake
open Lake DSL

package «tacenta-model» where

@[default_target]
lean_lib «Model» where
  globs := #[Glob.submodules `Model]

@[default_target]
lean_lib «Properties» where
  globs := #[Glob.submodules `Properties]

-- A default target too, so that `lake build` compiles `Vectors.lean` and a
-- change that breaks the vector generator fails the model build rather than
-- waiting for the next `regenerate-vectors.sh` run to find it.
@[default_target]
lean_exe genvectors where
  root := `Vectors

-- The model's half of the differential harness, a default target for the same
-- reason: a model change that breaks it fails the model build rather than
-- waiting for the Rust side to find it. See `Difftest.lean`.
@[default_target]
lean_exe difftest where
  root := `Difftest

-- The refuted-record walk as an executable (`Model/AxiomAudit.lean`'s `main`):
-- `tacenta-proofs/scripts/check-refuted-records.sh` runs it once per
-- translation audit module, loading the module's import closure at run time
-- with `importModules`, so that nothing a module of the tree declares is
-- parsed where the walk is called. Not a default target: it is built by that
-- script, and the model's own build has no use for it.
lean_exe «refuted-records» where
  root := `Model.AxiomAudit
  -- `importModules` needs the interpreter's symbols linked in.
  supportInterpreter := true
