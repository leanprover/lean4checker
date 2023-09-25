import Lake
open Lake DSL

package «lean4checker» where

@[default_target]
lean_lib «Lean4Checker» where

@[default_target]
lean_exe «lean4checker» where
  root := `Main
  supportInterpreter := true
