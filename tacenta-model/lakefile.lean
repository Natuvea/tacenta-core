import Lake
open Lake DSL

package «tacenta-model» where

@[default_target]
lean_lib «Model» where
  globs := #[Glob.submodules `Model]

@[default_target]
lean_lib «Properties» where
  globs := #[Glob.submodules `Properties]

lean_exe genvectors where
  root := `Vectors
