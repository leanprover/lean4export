import Export
open Lean

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (imports, constants) := args.span (· != "--")
  let imports := imports.map fun mod => { module := Syntax.decodeNameLit ("`" ++ mod) |>.get! }
  let constants? := constants.tail?.map (·.map fun c => Syntax.decodeNameLit ("`" ++ c) |>.get!)
  let env ← importModules imports {}
  M.run env do
    for c in constants?.getD (env.constants.toList.map (·.1)) do
      let _ ← dumpConstant c
