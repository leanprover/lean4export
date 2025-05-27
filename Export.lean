import Lean
import Std.Data.HashMap.Basic

open Lean
open Std (HashMap)

instance : Hashable RecursorRule where
  hash r := hash (r.ctor, r.nfields, r.rhs)

structure Context where
  env : Environment

structure State where
  visitedNames : HashMap Name Nat := .insert {} .anonymous 0
  visitedLevels : HashMap Level Nat := .insert {} .zero 0
  visitedExprs : HashMap Expr Nat := {}
  visitedRecRules : HashMap RecursorRule Nat := {}
  visitedConstants : NameHashSet := {}

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

/-
Eliminate `mdata` nodes while dumping an expression.

When an `mdata` node is encountered, pass through it. For everything else, update `e`
IFF a sub-expression contained `mdata`.

returns `(had mdata, the expression with any mdata removed, e's export index)`
-/
@[inline]
partial def dumpExprAux (e : Expr) : M (Bool × Expr × Nat) := do
  /- If this is an mdata node, dump the inner item and return the expr without mdata -/
  if let .mdata _ e' := e then
    let (_, e'', idx) ← dumpExprAux e'
    return (true, e'', idx)
  /- If we've already seen this expression, use the cached data -/
  if let some idx := (← get).visitedExprs.get? e then
    return (false, e, idx)
  else
    let (ck, e, s) ←
      match e with
      | .mdata .. | .fvar .. | .mvar .. => unreachable!
      | .bvar i => pure (false, e, (return s!"#EV {i}"))
      | .sort l => pure (false, e, (return s!"#ES {← dumpLevel l}"))
      | .const n us => pure (false, e, (return s!"#EC {← dumpName n} {← seq <$> us.mapM dumpLevel}"))
      | .lit (.natVal i) => pure (false, e, (return s!"#ELN {i}"))
      | .lit (.strVal s) => pure (false, e, (return s!"#ELS {s.toUTF8.toList.map uint8ToHex |> seq}"))
      | .app f a =>
        let (f_rebuilt, f, f_idx) ← dumpExprAux f
        let (a_rebuilt, a, a_idx) ← dumpExprAux a
        let ck := f_rebuilt || a_rebuilt
        pure (ck, if ck then e.updateApp! f a else e, (return s!"#EA {f_idx} {a_idx}"))
      | .lam n d b bi =>
        let (d_rebuilt, d, d_idx) ← dumpExprAux d
        let (b_rebuilt, b, b_idx) ← dumpExprAux b
        let ck := (d_rebuilt || b_rebuilt)
        pure (ck, if ck then e.updateLambdaE! d b else e, (return s!"#EL {dumpInfo bi} {← dumpName n} {d_idx} {b_idx}"))
      | .letE n d v b _ =>
        let (d_rebuilt, d, d_idx) ← dumpExprAux d
        let (v_rebuilt, v, v_idx) ← dumpExprAux v
        let (b_rebuilt, b, b_idx) ← dumpExprAux b
        let ck := (d_rebuilt || v_rebuilt || b_rebuilt)
        pure (ck, if ck then e.updateLet! d v b else e, (return s!"#EZ {← dumpName n} {d_idx} {v_idx} {b_idx}"))
      | .forallE n d b bi =>
        let (d_rebuilt, d, d_idx) ← dumpExprAux d
        let (b_rebuilt, b, b_idx) ← dumpExprAux b
        let ck := (d_rebuilt || b_rebuilt)
        pure (ck, if ck then e.updateForallE! d b else e, (return s!"#EP {dumpInfo bi} {← dumpName n} {d_idx} {b_idx}"))
      | .proj s i e2 =>
        let (e_rebuilt, ex, e'_idx) ← dumpExprAux e2
        let ck := e_rebuilt
        pure (ck, if ck then (e.updateProj! ex) else e, (return s!"#EJ {← dumpName s} {i} {e'_idx}"))
    tryPrintE ck e s
where
  tryPrintE (hadMData: Bool) (e : Expr) (s : M String) : M (Bool × Expr × Nat) := do
    /- If the expression had `mdata` and was rebuilt, check the rebuilt expression
    against the cache once more -/
    if hadMData then
      if let some idx := (← get).visitedExprs.get? e then
      return (hadMData, e, idx)
    let idx := (← get).visitedExprs.size
    modify (fun st => { st with visitedExprs := st.visitedExprs.insert e idx })
    IO.println s!"{idx} {← s}"
    return (hadMData, e, idx)

@[inline]
def dumpExpr (e : Expr) : M Nat := do
  let (_, _, n) ← dumpExprAux e
  return n

def dumpHints : ReducibilityHints → String
  | .opaque => "O"
  | .abbrev => "A"
  | .regular n => s!"R {n}"

partial def dumpConstant (c : Name) : M Unit := do
  if (← get).visitedConstants.contains c then
    return
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  match (← read).env.find? c |>.get! with
  | .axiomInfo val => do
    if val.isUnsafe then
      return
    dumpDeps val.type
    IO.println s!"#AX {← dumpName c} {← dumpExpr val.type} {← seq <$> val.levelParams.mapM dumpName}"
  | .defnInfo val => do
    if val.safety != .safe then
      return
    dumpDeps val.type
    dumpDeps val.value
    IO.println s!"#DEF {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {dumpHints val.hints} {← seq <$> val.levelParams.mapM dumpName}"
  | .thmInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    IO.println s!"#THM {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {← seq <$> val.levelParams.mapM dumpName}"
  | .opaqueInfo val => do
    if val.isUnsafe then
      return
    dumpDeps val.type
    dumpDeps val.value
    IO.println s!"#OPAQ {← dumpName c} {← dumpExpr val.type} {← dumpExpr val.value} {← seq <$> val.levelParams.mapM dumpName}"
  | .quotInfo val =>
    dumpDeps val.type
    IO.println s!"#QUOT {← dumpName c} {← dumpExpr val.type} {← seq <$> val.levelParams.mapM dumpName}"
  | .inductInfo val => do
    if val.isUnsafe then
      return
    dumpDeps val.type
    for ctor in val.ctors do
      dumpDeps ((← read).env.find? ctor |>.get!.type)
    let indNameIdxs ← val.all.mapM dumpName
    let ctorNameIdxs ← val.ctors.mapM (fun ctor => dumpName ctor)
    let isRec := if val.isRec then 1 else 0
    let isNested := if val.isNested then 1 else 0
    IO.println s!"#IND {← dumpName c} {← dumpExpr val.type} {isRec} {isNested} {val.numParams} {val.numIndices} {indNameIdxs.length} {seq indNameIdxs} {val.numCtors} {seq ctorNameIdxs} {← seq <$> val.levelParams.mapM dumpName}"
  | .ctorInfo val =>
    if val.isUnsafe then
      return
    dumpDeps val.type
    IO.println s!"#CTOR {← dumpName c} {← dumpExpr val.type} {← dumpName val.induct} {val.cidx} {val.numParams} {val.numFields} {← seq <$> val.levelParams.mapM dumpName}"
  | .recInfo val =>
    if val.isUnsafe then
      return
    dumpDeps val.type
    let indNameIdxs ← val.all.mapM dumpName
    let k := if val.k then 1 else 0
    let ruleIdxs ← val.rules.mapM (fun rule => dumpRecRule rule)
    IO.println s!"#REC {← dumpName c} {← dumpExpr val.type} {indNameIdxs.length} {seq indNameIdxs} {val.numParams} {val.numIndices} {val.numMotives} {val.numMinors} {ruleIdxs.length} {seq ruleIdxs} {k} {← seq <$> val.levelParams.mapM dumpName}"
where
  dumpDeps e := do
    for c in e.getUsedConstants do
      dumpConstant c
  dumpRecRule (rule : RecursorRule) : M Nat := getIdx rule (·.visitedRecRules) ({ · with visitedRecRules := · }) do
    dumpDeps (rule.rhs)
    return s!"#RR {← dumpName rule.ctor} {rule.nfields} {← dumpExpr rule.rhs}"
