A simple declaration exporter for Lean 4 using the [Lean 4 NDJSON export format](./format_ndjson.md)

## How to Run

1. Build lean4export with `lake build`

2. Call the `lean4export` binary with the correct lake env set up.

```sh
lake env <path to lean4export binary> <lean file without .lean suffix>+
```

For example, let's assume we're working in the `mathlib4` directory, with the following structure: 
```
|__ mathlib4 (*we are here)
|__ lean4export
```

We can invoke the exporter on the "top level" mathlib file and export mathlib with the following command:
```sh
lake env ../.lake/build/bin/lean4export Mathlib > out.ndjson
```
This exports all contents of the given Lean module (here just the top level `Mathlib` module in the `Mathlib.lean` file), and all the contents of that module's transitive dependencies. 

More than one module can be passed to the initial invocation by including more than one name (separated with a space).

### Options

The option `--export-unsafe` can be used to include unsafe declarations in the export file. This may be useful for testing and debugging other tools, where unsafe declarations can serve as negative examples.

The option `--export-mdata"` can be used to include `Expr.mdata` items in the export file, which are removed by default as they should not have an effect on type checking.

The option `--help` prints usage information and then exits.

The default behavior of exporting all constants can be modified by describing specific constants to export. Lean4export will import only those constants and their transitive dependencies.

 * The argument `--all-theorems <ModuleName>` will include all theorems in a specific module.
 * The argument `--` can be followed by a list of specific constants.

As an example, this command will export only the constants necessary to support the theorem `EuclideanGeometry.dist_inversion_inversion` as well all the theorems in Mathlib's `Mathlib/Algebra/Module/NatInt.lean` module.
```sh
lake env ../.lake/build/bin/lean4export Mathlib --theorems-from Mathlib.Algebra.Module.NatInt -- EuclideanGeometry.dist_inversion_inversion
```

