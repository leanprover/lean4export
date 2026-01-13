import Lean
import Std.Data.HashMap.Basic

open Lean
open Std (HashMap)

def Lean.BinderInfo.toJson : BinderInfo → Json
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def Lean.ReducibilityHints.toJson : ReducibilityHints → Json
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular n => .mkObj [("regular", n.toNat)]

def Lean.QuotKind.toJson : QuotKind → Json
  | type => "type"
  | ctor => "ctor"
  | lift => "lift"
  | ind => "ind"

def Lean.DefinitionSafety.toJson : DefinitionSafety → Json
  | «unsafe» => "unsafe"
  | safe => "safe"
  | «partial» => "partial"

def Lean.KVMap.toJson (kvs: Lean.KVMap) : Json :=
  .mkObj <| kvs.entries.map (fun (k, v) => (k.toString, reprStr v))

def Nat.toBytesLE (n : Nat) : ByteArray :=
  if n = 0 then
    ByteArray.empty.push 0
  else
    let rec aux (n : Nat) (acc : ByteArray) : ByteArray :=
      if n = 0 then
        acc
      else
        aux (n / 256) (acc.push <| UInt8.ofNat <| n % 256)
    aux n ByteArray.empty

instance : ToJson UInt8 where
  toJson n := ToJson.toJson n.toNat

structure Context where
  env : Environment

structure State where
  visitedNames : HashMap Name Nat := HashMap.emptyWithCapacity 200000 |>.insert .anonymous 0
  visitedLevels : HashMap Level Nat := HashMap.emptyWithCapacity 1000 |>.insert .zero 0
  visitedExprs : HashMap Expr Nat := HashMap.emptyWithCapacity 10000000
  visitedConstants : NameHashSet := {}
  noMDataExprs : HashMap ExprStructEq Expr := HashMap.emptyWithCapacity
  exportMData : Bool := false
  exportUnsafe : Bool := false

abbrev M := ReaderT Context <| StateT State IO

def M.run (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {}) do
    ReaderT.run (r := { env }) do
      act

/--
For a given primitive (name, level, expr) to be exported:
IFF it's been seen before, return its index within the export file
IFF it has not been seen before, add it to the cache, print it into the export, and return its cache index.
-/
@[inline]
def getIdx [Hashable α] [BEq α] (x : α) (getM : State → HashMap α Nat) (setM : State → HashMap α Nat → State) (rec : M Json) : M Nat := do
  let m ← getM <$> get
  if let some idx := m[x]? then
    return idx
  let s ← rec
  let m ← getM <$> get
  let idx := m.size
  IO.println (s.setObjVal! "i" idx).compress
  modify fun st => setM st ((getM st).insert x idx)
  return idx

def dumpName (n : Name) : M Nat := getIdx n (·.visitedNames) ({ · with visitedNames := · }) do
  match n with
  | .anonymous => unreachable!
  | .str n s =>
    return .mkObj [
      ("str", .mkObj [
        ("pre", ← dumpName n),
        ("str", s)
      ])
    ]
  | .num n i =>
    return .mkObj [
      ("num", .mkObj [
        ("pre", ← dumpName n),
        ("i", i)
      ])
    ]

def dumpLevel (l : Level) : M Nat := getIdx l (·.visitedLevels) ({ · with visitedLevels := · }) do
  match l with
  | .zero | .mvar _ => unreachable!
  | .succ l => return .mkObj [("succ", ← dumpLevel l)]
  | .max l1 l2 => return .mkObj [("max", Json.arr #[← dumpLevel l1, ← dumpLevel l2])]
  | .imax l1 l2 => return .mkObj [("imax", Json.arr #[← dumpLevel l1, ← dumpLevel l2])]
  | .param n => return .mkObj [("param", ← dumpName n)]

def dumpUparams (uparams : List Name) : M Json := do
  let nameIdxs ← uparams.mapM dumpName
  let _ ← (uparams.map (Level.param)).mapM dumpLevel
  pure nameIdxs.toJson

def dumpNames (uparams : List Name) : M Json := do
  let nameIdxs ← uparams.mapM dumpName
  return nameIdxs.toJson

def removeMData (e : Expr) : M Expr := do
  if let some x := (← get).noMDataExprs[ExprStructEq.mk e]? then
    return x
  let e' ← match e with
  | .mdata _ e' => removeMData e'
  | .fvar .. | .mvar ..=> unreachable!
  | .bvar .. | .sort .. | .const .. | .lit _ => pure e
  | .app f a =>
    pure <| e.updateApp! (← removeMData f) (← removeMData a)
  | .lam _ d b _ =>
    pure <| e.updateLambdaE! (← removeMData d) (← removeMData b)
  | .letE _ d v b nonDep =>
    pure <| e.updateLet! (← removeMData d) (← removeMData v) (← removeMData b) nonDep
  | .forallE _ d b _ =>
    pure <| e.updateForallE! (← removeMData d) (← removeMData b)
  | .proj _ _ e2 =>
    pure <| e.updateProj! (← removeMData e2)
  modify (fun st => { st with noMDataExprs := st.noMDataExprs.insert ⟨e⟩ e' })
  pure e'

partial def dumpExprAux (e : Expr) : M Nat := do
  getIdx e (·.visitedExprs) ({ · with visitedExprs := · }) do
    match e with
    | .fvar .. | .mvar .. => panic! "cannot export free variables or metavariables"
    | .mdata a e' =>
      return .mkObj [
        ("mdata", .mkObj [
            ("data", a.toJson),
            ("expr", ← dumpExprAux e')
        ])
      ]
    | .bvar i => return .mkObj [("bvar", .mkObj [("deBruijnIndex", i)])]
    | .lit (.natVal i) => return .mkObj [("natVal", s!"{i}")]
    | .lit (.strVal s) => return .mkObj [("strVal", s)]
    | .sort l => return .mkObj [("sort", .mkObj [("u", ← dumpLevel l)])]
    | .const n us => return .mkObj [
      ("const", .mkObj [
        ("declName", ← dumpName n),
        ("us", (← us.mapM dumpLevel).toJson)
      ])
    ]
    | .app f a => return .mkObj [
      ("app", .mkObj [
        ("fn", ← dumpExprAux f),
        ("arg", ← dumpExprAux a)
      ])
    ]
    | .lam n d b bi => return .mkObj [
      ("lam", .mkObj [
        ("binderName", ← dumpName n),
        ("binderType", ← dumpExprAux d),
        ("body", ← dumpExprAux b),
        ("binderInfo", bi.toJson)
      ])
    ]
    | .forallE n d b bi => return .mkObj [
      ("forallE", .mkObj [
        ("binderName", ← dumpName n),
        ("binderType", ← dumpExprAux d),
        ("body", ← dumpExprAux b),
        ("binderInfo", bi.toJson)
      ])
    ]
    | .letE n d v b nondep => return .mkObj [
      ("letE", .mkObj [
        ("declName", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("value", ← dumpExprAux v),
        ("body", ← dumpExprAux b),
        ("nondep", nondep)
      ])
    ]
    | .proj s i e => return .mkObj [
      ("proj", .mkObj [
        ("typeName", ← dumpName s),
        ("idx", i),
        ("struct", ← dumpExprAux e)
      ])
    ]

def dumpExpr (e : Expr) : M Nat := do
  let aux (e : Expr) : M Expr := do
    modify (fun st => { st with noMDataExprs := HashMap.emptyWithCapacity })
    removeMData e
  dumpExprAux <| ← if (← get).exportMData then pure e else aux e

partial def dumpConstant (c : Name) : M Unit := do
  let declar := ((← read).env.find? c).get!
  if (declar.isUnsafe && !(← get).exportUnsafe) || (← get).visitedConstants.contains c then
    return
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  match declar with
  | .axiomInfo val => do
    dumpDeps val.type
    IO.println <| Json.mkObj [
      ("axiomInfo", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("isUnsafe", val.isUnsafe)
      ])
    ] |>.compress
  | .defnInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    IO.println <| Json.mkObj [
      ("defnInfo", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("hints", val.hints.toJson),
        ("safety", val.safety.toJson),
        ("all", ← dumpNames val.all)
      ])
    ] |>.compress
   | .thmInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    IO.println <| Json.mkObj [
      ("thmInfo", .mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("all", ← dumpNames val.all)
      ])
    ] |>.compress
  | .opaqueInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    IO.println <| Json.mkObj [
      ("opaqueInfo", .mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("all", ← dumpNames val.all)
      ])
    ] |>.compress
  | .quotInfo val =>
    dumpDeps val.type
    IO.println <| Json.mkObj [
      ("quotInfo", .mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("kind", val.kind.toJson)
      ])
    ] |>.compress
  | .inductInfo val => do
    dumpDeps val.type
    IO.println <| Json.mkObj [
      ("inductInfo", .mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("numParams", val.numParams),
        ("numIndices", val.numIndices),
        ("all", ← dumpNames val.all),
        ("ctors", ← dumpNames val.ctors),
        ("numNested", val.numNested),
        ("isRec", val.isRec),
        ("isReflexive", val.isReflexive),
        ("isUnsafe", val.isUnsafe),
      ])
    ] |>.compress
    for ctor in val.ctors do
      dumpConstant ctor
  | .ctorInfo val =>
    dumpDeps val.type
    IO.println <| Json.mkObj [
      ("ctorInfo", .mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("induct", ← dumpName val.induct),
        ("cidx", val.cidx),
        ("numParams", val.numParams),
        ("numFields", val.numFields),
        ("isUnsafe", val.isUnsafe)
      ])
    ] |>.compress
  | .recInfo val =>
    dumpDeps val.type
    IO.println <| Json.mkObj [
      ("recInfo", .mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("all", ← dumpNames val.all),
        ("numParams", val.numParams),
        ("numIndices", val.numIndices),
        ("numMotives", val.numMotives),
        ("numMinors", val.numMinors),
        ("rules", (← val.rules.mapM dumpRecRule).toJson),
        ("k", val.k),
        ("isUnsafe", val.isUnsafe),
      ])
    ] |>.compress
where
  dumpDeps e := do
    for c in e.getUsedConstants do
      dumpConstant c
  /- Return these for inclusion inline with the exported `recInfo`. -/
  dumpRecRule (rule : RecursorRule) : M Json := do
    dumpDeps (rule.rhs)
    return Json.mkObj [
      ("ctor", ← dumpName rule.ctor),
      ("nfields", rule.nfields),
      ("rhs", ← dumpExpr rule.rhs),
    ]
