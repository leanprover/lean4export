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
This exports the contents of the given Lean module (here just the top level `Mathlib` module in the `Mathlib.lean` file), and its transitive dependencies. A specific list of declarations to be exported from these modules can be given after a separating `--`, and more than one module can be passed to the initial invocation by including more than one name (separted with a space).

### Options

The option `--export-unsafe` can be used to include unsafe declarations in the export file. This may be useful for testing and debugging other tools, where unsafe declarations can serve as negative examples.

The option `--export-mdata"` can be used to include `Expr.mdata` items in the export file, which are removed by default as they should not have an effect on type checking.
