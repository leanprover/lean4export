import Lean
import Std.Data.HashMap.Basic

open Lean
open Std (HashMap)

instance instHashableRecursorRule : Hashable RecursorRule where
  hash r := hash (r.ctor, r.nfields, r.rhs)

structure Context where
  env : Environment

structure State where
  visitedNames : HashMap Name Nat := .insert {} .anonymous 0
  visitedLevels : HashMap Level Nat := .insert {} .zero 0
  visitedExprs : HashMap Expr Nat := {}
  visitedRecRules : HashMap RecursorRule Nat := {}
  visitedConstants : NameHashSet := {}
  noMDataExprs : HashMap Expr Expr := {}
  exportUnsafe : Bool := false

abbrev M := ReaderT Context <| StateT State IO

def M.run (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {}) do
    ReaderT.run (r := { env }) do
      act

@[inline]
def getIdx [Hashable α] [BEq α] (x : α) (getM : State → HashMap α Nat) (setM : State → HashMap α Nat → State) (rec : M String) : M Nat := do
  let m ← getM <$> get
  if let some idx := m[x]? then
    return idx
  let s ← rec
  let m ← getM <$> get
  let idx := m.size
  IO.println s!"{idx} {s}"
  modify fun st => setM st ((getM st).insert x idx)
  return idx

def dumpName (n : Name) : M Nat := getIdx n (·.visitedNames) ({ · with visitedNames := · }) do
  match n with
  | .anonymous => unreachable!
  | .str n s => return s!"#NS {← dumpName n} {s}"
  | .num n i => return s!"#NI {← dumpName n} {i}"

def dumpLevel (l : Level) : M Nat := getIdx l (·.visitedLevels) ({ · with visitedLevels := · }) do
  match l with
  | .zero | .mvar _ => unreachable!
  | .succ l => return s!"#US {← dumpLevel l}"
  | .max l1 l2 => return s!"#UM {← dumpLevel l1} {← dumpLevel l2}"
  | .imax l1 l2 => return s!"#UIM {← dumpLevel l1} {← dumpLevel l2}"
  | .param n => return s!"#UP {← dumpName n}"

def seq [ToString α] (xs : List α) : String :=
  xs.map toString |> String.intercalate " "

def dumpInfo : BinderInfo → String
  | .default => "#BD"
  | .implicit => "#BI"
  | .strictImplicit => "#BS"
  | .instImplicit => "#BC"

def uint8ToHex (c : UInt8) : String :=
  let d2 := c / 16
  let d1 := c % 16
  (hexDigitRepr d2.toNat ++ hexDigitRepr d1.toNat).toUpper

def removeMData (e : Expr) : M Expr := do
  if let some x := (← get).noMDataExprs[e]? then
    return x
  let e' ← match e with
  | .mdata _ e' => removeMData e'
  | .fvar .. | .mvar ..=> unreachable!
  | .bvar .. | .sort .. | .const .. | .lit _ => pure e
  | .app f a =>
    pure <| e.updateApp! (← removeMData f) (← removeMData a)
  | .lam _ d b _ =>
    pure <| e.updateLambdaE! (← removeMData d) (← removeMData b)
  | .letE _ d v b _ =>
    pure <| e.updateLetE! (← removeMData d) (← removeMData v) (← removeMData b)
  | .forallE _ d b _ =>
    pure <| e.updateForallE! (← removeMData d) (← removeMData b)
  | .proj _ _ e2 =>
    pure <| e.updateProj! (← removeMData e2)
  modify (fun st => { st with noMDataExprs := st.noMDataExprs.insert e e' })
  pure e'

partial def dumpExprAux (e : Expr) : M Nat := do
  getIdx e (·.visitedExprs) ({ · with visitedExprs := · }) do
    match e with
    | .bvar i => return s!"#EV {i}"
    | .sort l => return s!"#ES {← dumpLevel l}"
    | .const n us =>
      return s!"#EC {← dumpName n} {← seq <$> us.mapM dumpLevel}"
    | .app f e => return s!"#EA {← dumpExprAux f} {← dumpExprAux e}"
    | .lam n d b bi => return s!"#EL {dumpInfo bi} {← dumpName n} {← dumpExprAux d} {← dumpExprAux b}"
    | .letE n d v b _ => return s!"#EZ {← dumpName n} {← dumpExprAux d} {← dumpExprAux v} {← dumpExprAux b}"
    | .forallE n d b bi => return s!"#EP {dumpInfo bi} {← dumpName n} {← dumpExprAux d} {← dumpExprAux b}"
    | .mdata .. | .fvar .. | .mvar .. => unreachable!
    -- extensions compared to Lean 3
    | .proj s i e => return s!"#EJ {← dumpName s} {i} {← dumpExprAux e}"
    | .lit (.natVal i) => return s!"#ELN {i}"
    | .lit (.strVal s) => return s!"#ELS {s.toUTF8.toList.map uint8ToHex |> seq}"

def dumpExpr (e : Expr) : M Nat := do
  dumpExprAux (← removeMData e)

def dumpHints : ReducibilityHints → String
  | .opaque => "O"
  | .abbrev => "A"
  | .regular n => s!"R {n}"

def dumpUparams (uparams : List Name) : M (List Nat) := do
  let nameIdxs ← uparams.mapM dumpName
  let _ ← (uparams.map (.param)).mapM dumpLevel
  pure nameIdxs

partial def dumpConstant (c : Name) : M Unit := do
  let declar := ((← read).env.find? c).get!
  if (declar.isUnsafe && !(← get).exportUnsafe) || (← get).visitedConstants.contains c then
    return
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  match declar with
  | .axiomInfo val => do
    IO.println s!"#AX {← dumpName c} {← dumpExpr val.type} {← seq <$> dumpUparams val.levelParams}"
  | .defnInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    IO.println s!"#DEF {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {dumpHints val.hints} {← seq <$> dumpUparams val.levelParams}"
  | .thmInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    IO.println s!"#THM {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {← seq <$> dumpUparams val.levelParams}"
  | .opaqueInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    IO.println s!"#OPAQ {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {← seq <$> dumpUparams val.levelParams}"
  | .quotInfo val =>
    dumpDeps val.type
    IO.println s!"#QUOT {← dumpName c} {← dumpExpr val.type} {← seq <$> dumpUparams val.levelParams}"
  | .inductInfo val => do
    dumpDeps val.type
    let indNameIdxs ← val.all.mapM dumpName
    let ctorNameIdxs ← val.ctors.mapM (fun ctor => dumpName ctor)
    let isReflexive := if val.isReflexive then 1 else 0
    let isRec := if val.isRec then 1 else 0
    IO.println s!"#IND {← dumpName c} {← dumpExpr val.type} {isReflexive} {isRec} {val.numNested} {val.numParams} {val.numIndices} {indNameIdxs.length} {seq indNameIdxs} {val.numCtors} {seq ctorNameIdxs} {← seq <$> dumpUparams val.levelParams}"
    /-
    We now have at least one inductive exported for which the constructor is never invoked, but
    they're needed for the recursors.
    -/
    for ctor in val.ctors do
      dumpConstant ctor
  | .ctorInfo val =>
    dumpDeps val.type
    IO.println s!"#CTOR {← dumpName c} {← dumpExpr val.type} {← dumpName val.induct} {val.cidx} {val.numParams} {val.numFields} {← seq <$> dumpUparams val.levelParams}"
  | .recInfo val =>
    dumpDeps val.type
    let indNameIdxs ← val.all.mapM dumpName
    let k := if val.k then 1 else 0
    let ruleIdxs ← val.rules.mapM (fun rule => dumpRecRule rule)
    IO.println s!"#REC {← dumpName c} {← dumpExpr val.type} {indNameIdxs.length} {seq indNameIdxs} {val.numParams} {val.numIndices} {val.numMotives} {val.numMinors} {ruleIdxs.length} {seq ruleIdxs} {k} {← seq <$> dumpUparams val.levelParams}"
where
  dumpDeps e := do
    for c in e.getUsedConstants do
      dumpConstant c
  dumpRecRule (rule : RecursorRule) : M Nat := getIdx rule (·.visitedRecRules) ({ · with visitedRecRules := · }) do
    dumpDeps (rule.rhs)
    return s!"#RR {← dumpName rule.ctor} {rule.nfields} {← dumpExpr rule.rhs}"
