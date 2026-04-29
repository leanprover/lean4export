import Export
open Lean

/--
Whether to export all constants, all the constants in the specified modules
(including private and internal constants) or specific named constants.
-/
inductive ConstantExportSetting where
  | all : ConstantExportSetting
  | allInModules : ConstantExportSetting
  | specificConstants : List Name → ConstantExportSetting

structure Opts extends Flags where
  modules : Array Name
  constantExport : ConstantExportSetting

def parseOpts : List String → Except String Opts := go {} #[] .none
where
  go (flags : Flags) (modules : Array Name) (constantExport : Option ConstantExportSetting) : List String → Except String Opts
    | "--" :: rest => do
      unless constantExport = .none do
        throw s!"Cannot describe individual constants using `--` in combination with --all-module-constants"
      let constants ← rest.mapM fun constant => do
        let .some name := Syntax.decodeNameLit ("`" ++ constant)
          | throw s!"Could not turn constant `{constant}` into an identifier"
        return name
      return ⟨flags, modules, .specificConstants constants⟩
    | [] => .ok ⟨flags, modules, constantExport.getD .all⟩
    | "-h" :: rest => go { flags with printHelp := true } modules constantExport rest
    | "--help" :: rest => go { flags with printHelp := true } modules constantExport rest
    | "--export-mdata" :: rest => go { flags with exportMData := true } modules constantExport rest
    | "--export-unsafe" :: rest => go { flags with exportUnsafe := true } modules constantExport rest
    | "-m" :: rest => do
      unless constantExport = .none do
        throw s!"Redundant or conflicting constant export settings"
      go flags modules (.some .allInModules) rest
    | "--all-module-constants" :: rest => do
      unless constantExport = .none do
        throw s!"Redundant or conflicting constant export settings"
      go flags modules (.some .allInModules) rest
    | mod :: rest => do
      let .some name := Syntax.decodeNameLit ("`" ++ mod)
        | throw s!"Could not turn module name `{mod}` to an identifier"
      go flags (modules.push name) constantExport rest

def usage := "usage: lean4export <modules> [-h | --help]
                   [--export-mdata] [--export-unsafe]
                   [-m | --all-module-constants | -- <constants>]"

/--
Get all suitable constants defined in a module
-/
def pickConstants (flags : Flags) (env : Environment) (mod: Name) : Array Name :=
  let moduleIdx := env.getModuleIdx? mod |>.get!

  -- Grab all constants from the module
  let moduleData := env.header.moduleData[moduleIdx]!
  moduleData.constants
    |>.filterMap (fun const =>
      -- include all non-internal constants AND constants that are non-internal but private
      let constNameWithPrivateRemoved := const.name.components.filter (· != `_private)
      if constNameWithPrivateRemoved.any (·.isInternal) then
        .none
      -- omit internal constants that are partial or unsafe
      else if const.isUnsafe && not flags.exportUnsafe then
        .none
      else
        .some const.name)


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
    let constants := match constants with
      | .all => env.constants.toList.map Prod.fst |>.filter (Name.isInternal · |> not)
      | .allInModules => imports.foldl (init := NameSet.empty)
          (fun set mod => pickConstants flags env mod |>.foldl (init := set) NameSet.insert)
          |>.toList
      | .specificConstants c => c
    M.run flags env do
      initState env
      dumpMetadata
      for c in constants do
        modify (fun st => { st with noMDataExprs := {} })
        dumpConstant c
