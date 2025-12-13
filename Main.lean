import Export
open Lean

def semver := "3.0.0"

def exportMetadata : Json :=
  let leanMeta := Json.mkObj [
    ("version", versionString),
    ("githash", githash)
  ]
  let exporterMeta := Json.mkObj [
    ("name", "lean4export"),
    ("version", semver)
  ]

  Json.mkObj [
    ("meta", Json.mkObj [
      ("exporter", exporterMeta),
      ("lean", leanMeta)
    ])
  ]

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (opts, args) := args.partition (fun s => s.startsWith "--" && s.length ≥ 3)
  let (imports, constants) := args.span (· != "--")
  let imports := imports.toArray.map fun mod => { module := Syntax.decodeNameLit ("`" ++ mod) |>.get! }
  let env ← importModules imports {}
  let constants := match constants.tail? with
    | some cs => cs.map fun c => Syntax.decodeNameLit ("`" ++ c) |>.get!
    | none    => env.constants.toList.map Prod.fst |>.filter (!·.isInternal)
  M.run env do
    modify (fun st => { st with
      exportMData  := opts.any  (· == "--export-mdata")
      exportUnsafe := opts.any (· == "--export-unsafe")
    })
    IO.println exportMetadata.compress
    for c in constants do
      modify (fun st => { st with noMDataExprs := {} })
      let _ ← dumpConstant c
