import Export
open Lean

def semver := "2.1.0"

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (opts, args) := args.partition (fun s => s.startsWith "--" && s.length ≥ 3)
  let (imports, constants) := args.span (· != "--")
  let imports := imports.toArray.map fun mod => { module := Syntax.decodeNameLit ("`" ++ mod) |>.get! }
  let env ← importModules imports {}
  let constants := match constants.tail? with
    | some cs => cs.map fun c => Syntax.decodeNameLit ("`" ++ c) |>.get!
    | none    => env.constants.toList.map Prod.fst |>.filter (!·.isInternal)
  let runResult ← M.run env do
    modify (fun st => { st with exportUnsafe := opts.any (· == "--export-unsafe") })
    IO.println semver
    for c in constants do
      modify (fun st => { st with noMDataExprs := {} })
      let _ ← dumpConstant c
  match runResult with
  | .ok _ => return 0
  | e@(.error _) =>
    IO.eprintln s!"{e}"
    return 1
