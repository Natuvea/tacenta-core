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
