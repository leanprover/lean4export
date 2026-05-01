import Export
import Export.CLIArgs
open Lean

def usage := "Usage:
  lean4export (-h | --help)
  lean4export [--export-mdata] [--export-unsafe]
              [MODULE_NAME...] [(--all-theorems MODULE_NAME)...]
              [-- CONSTANT...]"

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match parseOpts args with
  | .error msg => do
    IO.eprintln s!"{msg}\n\n{usage}\n"
    return 1

  | .ok opts => do
    if opts.printHelp then
      IO.eprintln usage
      return 0

    let env ← importModules (opts.modules.map ({ module := ·.name })) {}
    let missingConstants ← opts.constants.filterM fun name => do
      if env.constants.contains name then
        return false
      IO.eprintln s!"Required constant {name} not found in environment"
      return true
    if missingConstants.length > 0 then
      return 1

    let constants := getRootConstants env opts

    M.run opts.toFlags env do
      initState env
      dumpMetadata
      for c in constants do
        modify (fun st => { st with noMDataExprs := {} })
        dumpConstant c
    return 0
