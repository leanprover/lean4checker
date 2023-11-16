import Lake
open Lake DSL

package «lean4checker» where

 @[default_target]
lean_lib «Lean4Checker» where
  globs := #[.andSubmodules `Lean4Checker]

@[default_target]
lean_exe «lean4checker» where
  root := `Main
  supportInterpreter := true

@[default_target]
lean_lib «Lean4CheckerTests» where
  globs := #[.andSubmodules `Lean4CheckerTests]
