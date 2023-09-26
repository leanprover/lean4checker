import Lake
open Lake DSL

package «lean4checker» { }

@[default_target]
lean_lib «Lean4Checker» { }

@[default_target]
lean_exe «lean4checker» {
  root := `Main
  supportInterpreter := true
}
