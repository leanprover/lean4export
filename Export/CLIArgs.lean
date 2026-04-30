module

public import Lean
public import Export.Flags
open Lean

/--
A command-line mention of a module can instruct lean4export to load a module,
or it can add all of the module's theorems to the root set of constants to
export.
-/
public structure Include where
  name : Name
  includeAllTheorems : Bool
deriving Repr

public structure LeanExportOpts extends Flags where
  modules : Array Include
  constants : List Name
deriving Repr

public def parseOpts : List String → Except String LeanExportOpts := go {} #[]
where
  go (flags : Flags) (modules : Array Include) : List String → Except String LeanExportOpts
    | "--" :: [] =>
      throw "The argument `--` must be followed by at least one constant"
    | "--" :: rest => do
      let constants ← rest.mapM fun constant => do
        let .some name := Syntax.decodeNameLit ("`" ++ constant)
          | throw s!"Could not turn constant `{constant}` into an identifier"
        return name
      return ⟨flags, modules, constants⟩
    | [] =>
      if modules.size = 0 && !flags.printHelp then
        throw "At least one module must be specified"
      else
        return ⟨flags, modules, []⟩
    | "-h" :: rest => go { flags with printHelp := true } modules rest
    | "--help" :: rest => go { flags with printHelp := true } modules rest
    | "--export-mdata" :: rest => go { flags with exportMData := true } modules rest
    | "--export-unsafe" :: rest => go { flags with exportUnsafe := true } modules rest
    | "--all-theorems" :: mod :: rest => do
      let .some name := Syntax.decodeNameLit ("`" ++ mod)
        | throw s!"Could not turn module name `{mod}` to an identifier"
      go flags (modules.push ⟨name, true⟩) rest
    | mod :: rest => do
      let .some name := Syntax.decodeNameLit ("`" ++ mod)
        | throw s!"Could not turn module name `{mod}` to an identifier"
      go flags (modules.push ⟨name, false⟩) rest

public def LeanExportOpts.shouldExportEverything (opts : LeanExportOpts) : Bool :=
  !opts.printHelp && opts.constants.length = 0 && opts.modules.all (not ·.includeAllTheorems)

/--
From a command line configuration, gets the root set of constants that the
exported environment must support.
-/
public def getRootConstants (env : Environment) (opts : LeanExportOpts) : List Name :=
  if opts.shouldExportEverything then
    -- Export "everything" for some value of everything
    env.constants.toList.filterMap fun const =>
      if const.fst.isInternal then
        .none
      else if !opts.exportUnsafe && const.snd.isUnsafe then
        .none
      else
        .some const.fst

  else
    -- Export selected constants
    opts.modules.filter (·.includeAllTheorems)
      |>.map (·.name)
      |>.foldl (β := NameSet) (init := NameSet.ofList opts.constants) (fun set mod =>
        -- Get module data from environment
        let moduleIdx := env.getModuleIdx? mod |>.get!
        let moduleData := env.header.moduleData[moduleIdx]!

        -- Read all theorems (NOTE: includes private/internal theorems)
        let moduleTheorems := moduleData.constants
          |>.filterMap fun
            | .thmInfo thm => .some thm.name
            | _ => .none
        moduleTheorems.foldl (init := set) (fun set name => NameSet.insert set name))
      |>.toList
