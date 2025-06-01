A simple declaration exporter for Lean 4 using the [Lean 4 export format](https://ammkrn.github.io/type_checking_in_lean4/export_format.html)

## How to Run

```sh
$ lake exe lean4export <mods> [options] [-- <decls>]
```
This exports the contents of the given Lean modules, looked up in the core library or `LEAN_PATH` (as e.g. initialized by an outer `lake env`) and their transitive dependencies.
A specific list of declarations to be exported from these modules can be given after a separating `--`.
The option `--export-unsafe` can be used to include unsafe declarations in the export file. This may be useful for testing and debugging other tools, where unsafe declarations can serve as negative examples.


## Format Extensions

The following commands have been added to represent new features of the Lean 4 type system.

```
<eidx'> #EJ <nidx> <integer> <eidx>
```
A primitive projection of the `<integer>`-nth field of a value `<eidx>` of the record type `<nidx>`.
Example: the primitive projection corresponding to `Prod.snd` of the innermost bound variable
```
1 #NS 0 Prod
0 #EV 0
1 #EJ 1 1 0
```

```
<eidx'> #ELN <integer>
<eidx'> #ELS <hexhex>*
```
Primitive literals of type `Nat` and `String` (encoded as a sequence of UTF-8 bytes in hexadecimal), respectively.
Examples:
```
0 #ELN 1000000000000000
1 #ELS 68 69  # "hi"
```

```
<eidx'> #EZ <nidx> <eidx_1> <eidx_2> <eidx_3>
```
A binding `let <nidx> : <eidx_1> := <eidx_2>; <eidx_3>`.
Already supported by the Lean 3 export format, but not documented.
Example: the encoding of `let x : Nat := Nat.zero; x` is
```
1 #NS 0 x
2 #NS 0 Nat
0 #EC 2 
3 #NS 2 zero
1 #EC 3 
2 #EV 0
3 #EZ 1 0 1 2
```
