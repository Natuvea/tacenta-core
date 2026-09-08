import Lake
open Lake DSL

require «tacenta-model» from ".." / "tacenta-model"

package «tacenta-proofs» where

@[default_target]
lean_lib «Proofs» where
  globs := #[Glob.submodules `Proofs]
