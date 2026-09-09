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
