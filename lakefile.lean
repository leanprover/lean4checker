import Lake
open Lake DSL

package «redeclare» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Redeclare» {
  -- add library configuration options here
}

@[default_target]
lean_exe «redeclare» {
  root := `Main
}
