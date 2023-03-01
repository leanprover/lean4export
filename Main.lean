import Export
open Lean

def main (mods : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let imports := mods.map fun mod => { module := Syntax.decodeNameLit ("`" ++ mod) |>.get! }
  let env ← importModules imports {}
  M.run env do
    for c in env.constants.toList do
      let _ ← dumpConstant c.1
