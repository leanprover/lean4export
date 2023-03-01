import Lake
open Lake DSL

package «lean4export» {
  -- add package configuration options here
}

lean_lib Export {
  -- add library configuration options here
}

lean_lib Test {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4export» {
  root := `Main
  supportInterpreter := true
}
