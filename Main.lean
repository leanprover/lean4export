import Export
open Lean

/--
Whether to export all constants, all the constants in the specified modules
(including private and internal constants) or specific named constants.
-/
inductive ConstantExportSetting where
  | all : ConstantExportSetting
  | specificConstants : List Name → ConstantExportSetting

/--
Command line options for lean4export
-/
structure Opts extends Flags where
  modules : Array Name
  constantExport : ConstantExportSetting

def parseOpts : List String → Except String Opts := go {} #[]
where
  go (flags : Flags) (modules : Array Name) : List String → Except String Opts
    | "--" :: rest => do
      let constants ← rest.mapM fun constant => do
        let .some name := Syntax.decodeNameLit ("`" ++ constant)
          | throw s!"Could not turn constant `{constant}` into an identifier"
        return name
      return ⟨flags, modules, .specificConstants constants⟩
    | [] =>
      -- If `--all-module-theorems` is set, just include module theorems
      if flags.allModuleTheorems then
        .ok ⟨flags, modules, .specificConstants []⟩
      else
        .ok ⟨flags, modules, .all⟩
    | "-h" :: rest => go { flags with printHelp := true } modules rest
    | "--help" :: rest => go { flags with printHelp := true } modules rest
    | "--export-mdata" :: rest => go { flags with exportMData := true } modules rest
    | "--export-unsafe" :: rest => go { flags with exportUnsafe := true } modules rest
    | "--all-module-theorems" :: rest => do
      go { flags with allModuleTheorems := true } modules rest
    | mod :: rest => do
      let .some name := Syntax.decodeNameLit ("`" ++ mod)
        | throw s!"Could not turn module name `{mod}` to an identifier"
      go flags (modules.push name) rest

def usage := "usage: lean4export <modules> [-h | --help]
                   [--export-mdata] [--export-unsafe]
                   [--all-module-theorems] [-- <constants>]"

/--
Get all suitable constants defined in a module
-/
def pickConstants (env : Environment) (mod: Name) : Array Name :=
  let moduleIdx := env.getModuleIdx? mod |>.get!

  -- Grab all constants from the module
  let moduleData := env.header.moduleData[moduleIdx]!
  moduleData.constants
    |>.filterMap fun
      | .thmInfo thm => .some thm.name
      | _ => .none


def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  match parseOpts args with
  | .error msg => do
    IO.eprintln s!"{msg}\n\n{usage}\n"
    IO.Process.exit 1
  | .ok ⟨flags, imports, constants⟩ => do
    if flags.printHelp then
      IO.eprintln usage
      IO.Process.exit 0

    let env ← importModules (imports.map ({ module := · })) {}

    -- Determine what to export from the environment based on command-line options
    let moduleTheorems : NameSet :=
      if flags.allModuleTheorems then
        imports.foldl (init := NameSet.empty) fun set mod =>
          -- Get module data from environment
          let moduleIdx := env.getModuleIdx? mod |>.get!
          let moduleData := env.header.moduleData[moduleIdx]!

          -- Read all theorems (NOTE: includes private/internal theorems)
          let moduleTheorems := moduleData.constants
            |>.filterMap fun
              | .thmInfo thm => .some thm.name
              | _ => .none
          moduleTheorems.foldl (init := set) NameSet.insert
      else
        {}
    let constants := match constants with
      | .all => env.constants.toList.map Prod.fst |>.filter (Name.isInternal · |> not)
      | .specificConstants c => c ++ moduleTheorems.toList

    -- Dump selected constants and all dependencies
    M.run flags env do
      initState env
      dumpMetadata
      for c in constants do
        modify (fun st => { st with noMDataExprs := {} })
        dumpConstant c
