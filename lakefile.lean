import Lake
open Lake DSL

package lean4export

lean_lib Export
lean_lib Test

@[default_target]
lean_exe lean4export where
  root := `Main
  supportInterpreter := true
