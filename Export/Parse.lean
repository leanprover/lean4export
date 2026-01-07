/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Std.Data.HashMap
import Lean.Declaration
import Std.Internal.Parsec.String
import Lean.Data.Json.Parser

namespace Export

structure ExportedEnv where
  constMap : Std.HashMap Lean.Name Lean.ConstantInfo
  constOrder : Array Lean.Name
  deriving Inhabited

namespace Parse


open Std.Internal.Parsec Std.Internal.Parsec.String Lean

structure State where
  nameMap : Std.HashMap Nat Lean.Name := { (0, .anonymous) }
  levelMap : Std.HashMap Nat Lean.Level := { (0, .zero) }
  exprMap : Std.HashMap Nat Lean.Expr := {}
  recursorRuleMap : Std.HashMap Nat Lean.RecursorRule := {}
  constMap : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  constOrder : Array Lean.Name := #[]

abbrev M := StateT State <| Parser

def M.run (x : M α) (input : String) : Except String (α × State) := do
  Parser.run (StateT.run x {}) input

@[inline]
def fail (msg : String) : M α :=
  let err : Parser α := Std.Internal.Parsec.fail msg
  liftM err

@[inline]
def getName (nidx : Nat) : M Lean.Name := do
  let some n := (← get).nameMap[nidx]? | fail s!"Name not found {nidx}"
  return n

@[inline]
def addName (nidx : Nat) (n : Lean.Name) : M Unit := do
  modify fun s => { s with nameMap := s.nameMap.insert nidx n }

@[inline]
def getLevel (uidx : Nat) : M Lean.Level := do
  let some l := (← get).levelMap[uidx]? | fail s!"Level not found {uidx}"
  return l

@[inline]
def addLevel (uidx : Nat) (l : Lean.Level) : M Unit := do
  modify fun s => { s with levelMap := s.levelMap.insert uidx l }

@[inline]
def getExpr (eidx : Nat) : M Lean.Expr := do
  let some e := (← get).exprMap[eidx]? | fail s!"Expr not found {eidx}"
  return e

@[inline]
def addExpr (eidx : Nat) (e : Lean.Expr) : M Unit := do
  modify fun s => { s with exprMap := s.exprMap.insert eidx e }

@[inline]
def getRecursorRule (ridx : Nat) : M Lean.RecursorRule := do
  let some r := (← get).recursorRuleMap[ridx]? | fail s!"RecursorRule not found {ridx}"
  return r

@[inline]
def addRecursorRule (ridx : Nat) (r : Lean.RecursorRule) : M Unit := do
  modify fun s => { s with recursorRuleMap := s.recursorRuleMap.insert ridx r }

@[inline]
def addConst (name : Lean.Name) (d : Lean.ConstantInfo) : M Unit := do
  modify fun s => {
    s with
      constMap := s.constMap.insert name d
      constOrder := s.constOrder.push name
    }

@[inline]
def parseJsonObj : M (Std.TreeMap.Raw String Json) := do
  let (.obj obj) ← Json.Parser.anyCore | fail "Expected JSON object"
  return obj

@[inline]
def fetchIndex (obj : Std.TreeMap.Raw String Json) : M Nat := do
  let some (.num (idx : Nat)) := obj["i"]? | fail s!"Object is missing the index key: {obj.keys}"
  return idx

def parseNameStr (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["str"]? | fail s!"Name.str {idx} invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str {idx} invalid"
  let some (.str str) := data["str"]? | fail s!"Name.str {idx} invalid"

  let pre ← getName preIdx

  addName idx (.str pre str)

def parseNameNum (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["num"]? | fail s!"Name.num {idx} invalid"
  let some (.num (preIdx : Nat)) := data["pre"]? | fail s!"Name.str {idx} invalid"
  let some (.num (i : Nat)) := data["i"]? | fail s!"Name.num {idx} invalid"

  let pre ← getName preIdx

  addName idx (.num pre i)

def parseLevelSucc (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.num (lIdx : Nat)) := obj["succ"]? | fail s!"Level.succ {idx} invalid"
  let l ← getLevel lIdx

  addLevel idx (.succ l)

def parseLevelMax (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)]) := obj["max"]?
    | fail s!"Level.max {idx} invalid"

  let lhs ← getLevel lhsIdx
  let rhs ← getLevel rhsIdx

  addLevel idx (.max lhs rhs)

def parseLevelImax (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.arr #[.num (lhsIdx : Nat), .num (rhsIdx : Nat)]) := obj["imax"]?
    | fail s!"Level.imax {idx} invalid"

  let lhs ← getLevel lhsIdx
  let rhs ← getLevel rhsIdx

  addLevel idx (.imax lhs rhs)

def parseLevelParam (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.num (nIdx : Nat)) := obj["param"]? | fail s!"Level.param {idx} invalid"

  let n ← getName nIdx

  addLevel idx (.param n)

def parseExprBVar (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["bvar"]? | fail s!"Expr.bvar {idx} invalid"
  let some (.num (deBruijnIndex : Nat)) := data["deBruijnIndex"]? | fail s!"Expr.bvar {idx} invalid"

  addExpr idx (.bvar deBruijnIndex)

def parseExprSort (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["sort"]? | fail s!"Expr.sort {idx} invalid"
  let some (.num (uIdx : Nat)) := data["u"]? | fail s!"Expr.sort {idx} invalid"

  let u ← getLevel uIdx

  addExpr idx (.sort u)

def parseExprConst (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["const"]? | fail s!"Expr.const {idx} invalid"
  let some (.num (declNameIdx : Nat)) := data["declName"]? | fail s!"Expr.const {idx} invalid"
  let some (.arr usIdxs) := data["us"]? | fail s!"Expr.const {idx} invalid"

  let declName ← getName declNameIdx
  let us ← usIdxs.mapM fun uIdx => do
    let (.num (uIdx : Nat)) := uIdx | fail s!"Expr.const {idx} invalid"
    getLevel uIdx

  addExpr idx (.const declName us.toList)

def parseExprApp (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["app"]? | fail s!"Expr.app {idx} invalid"
  let some (.num (fnIdx : Nat)) := data["fn"]? | fail s!"Expr.app {idx} invalid"
  let some (.num (argIdx : Nat)) := data["arg"]? | fail s!"Expr.app {idx} invalid"

  let fn ← getExpr fnIdx
  let arg ← getExpr argIdx

  addExpr idx (.app fn arg)

def parseBinderInfo (info : String) : M BinderInfo :=
  match info with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | _ => fail s!"Invalid binder info: {info}"

def parseExprLam (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["lam"]? | fail s!"Expr.lam {idx} invalid"
  let some (.num (binderNameIdx : Nat)) := data["binderName"]? | fail s!"Expr.lam {idx} invalid"
  let some (.num (binderTypeIdx : Nat)) := data["binderType"]? | fail s!"Expr.lam {idx} invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.lam {idx} invalid"
  let some (.str binderInfoStr) := data["binderInfo"]? | fail s!"Expr.lam {idx} invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx
  let binderInfo ← parseBinderInfo binderInfoStr

  addExpr idx (.lam binderName binderType body binderInfo)

def parseExprForallE (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["forallE"]? | fail s!"Expr.forallE {idx} invalid"
  let some (.num (binderNameIdx : Nat)) := data["binderName"]? | fail s!"Expr.forallE {idx} invalid"
  let some (.num (binderTypeIdx : Nat)) := data["binderType"]? | fail s!"Expr.forallE {idx} invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.forallE {idx} invalid"
  let some (.str binderInfoStr) := data["binderInfo"]? | fail s!"Expr.forallE {idx} invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let body ← getExpr bodyIdx
  let binderInfo ← parseBinderInfo binderInfoStr

  addExpr idx (.forallE binderName binderType body binderInfo)

def parseExprLetE (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["letE"]? | fail s!"Expr.letE {idx} invalid"
  let some (.num (binderNameIdx : Nat)) := data["binderName"]? | fail s!"Expr.letE {idx} invalid"
  let some (.num (binderTypeIdx : Nat)) := data["binderType"]? | fail s!"Expr.letE {idx} invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"Expr.letE {idx} invalid"
  let some (.num (bodyIdx : Nat)) := data["body"]? | fail s!"Expr.letE {idx} invalid"
  let some (.bool nondep) := data["nondep"]? | fail s!"Expr.letE {idx} invalid"

  let binderName ← getName binderNameIdx
  let binderType ← getExpr binderTypeIdx
  let value ← getExpr bodyIdx
  let body ← getExpr bodyIdx

  addExpr idx (.letE binderName binderType value body nondep)

def parseExprProj (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["proj"]? | fail s!"Expr.proj {idx} invalid"
  let some (.num (typeNameIdx : Nat)) := data["typeName"]? | fail s!"Expr.proj {idx} invalid"
  let some (.num (projIdx : Nat)) := data["idx"]? | fail s!"Expr.proj {idx} invalid"
  let some (.num (structIdx : Nat)) := data["struct"]? | fail s!"Expr.proj {idx} invalid"

  let typeName ← getName typeNameIdx
  let struct ← getExpr structIdx

  addExpr idx (.proj typeName projIdx struct)

def parseExprNatLit (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.str natValStr) := obj["natVal"]? | fail s!"Expr.lit natVal {idx} invalid"
  let some natVal := String.toNat? natValStr | fail s!"Expr.lit natVal {idx} invalid"

  addExpr idx (.lit (.natVal natVal))

def parseExprStrLit (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.str strVal) := obj["strVal"]? | fail s!"Expr.lit strVal {idx} invalid"

  addExpr idx (.lit (.strVal strVal))

def parseExprMdata (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let idx ← fetchIndex obj
  let some (.obj data) := obj["mdata"]? | fail s!"Expr.mdata {idx} invalid"
  let some (.num (exprIdx : Nat)) := data["expr"]? | fail s!"Expr.mdata {idx} invalid"
  let some (.obj dataObj) := data["data"]? | fail s!"Expr.mdata {idx} invalid"
  let expr ← getExpr exprIdx

  -- TODO: Unclear how to perfectly recover with the current output format
  addExpr idx (.mdata {} expr)

def getNameList (idxs : Array Json) : M (List Name) := do
  idxs.toList.mapM fun idx => do
    let (.num (idx : Nat)) := idx | fail s!"failed to convert to name idx"
    getName idx

def parseAxiomInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["axiomInfo"]? | fail s!"axiomInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"axiomInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"axiomInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"axiomInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"axiomInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx

  addConst name <| .axiomInfo { name, levelParams, type, isUnsafe }

def parseDefnInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["defnInfo"]? | fail s!"defnInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"defnInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"defnInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"defnInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"defnInfo invalid"
  let some hints := data["hints"]? | fail s!"defnInfo invalid"
  let some (.str safetyStr) := data["safety"]? | fail s!"defnInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"defnInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let hints ←
    match hints with
    | .str "opaque" => pure .opaque
    | .str "abbrev" => pure .abbrev
    | .obj obj =>
      let some (.num (level : Nat)) := obj["regular"]? | fail s!"defnInfo invalid"
      pure <| .regular level.toUInt32
    | _ => fail s!"defnInfo invalid"
  let safety ←
    match safetyStr with
    | "unsafe" => pure .unsafe
    | "safe" => pure .safe
    | "partial" => pure .partial
    | _ => fail s!"Unknown safety parameter: {safetyStr}"
  let all ← getNameList allIdxs

  addConst name <| .defnInfo { name, levelParams, type, value, hints, safety, all }

def parseThmInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["thmInfo"]? | fail s!"thmInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"thmInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"thmInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"thmInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"thmInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"thmInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let all ← getNameList allIdxs

  addConst name <| .thmInfo { name, levelParams, type, value, all }

def parseOpaqueInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["opaqueInfo"]? | fail s!"opaqueInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"opaqueInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"opaqueInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"opaqueInfo invalid"
  let some (.num (valueIdx : Nat)) := data["value"]? | fail s!"opaqueInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"axiomInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"opaqueInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let value ← getExpr valueIdx
  let all ← getNameList allIdxs

  addConst name <| .opaqueInfo { name, levelParams, type, value, all, isUnsafe }

def parseQuotInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["quotInfo"]? | fail s!"opaqueInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"opaqueInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"opaqueInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"opaqueInfo invalid"
  let some (.str kindStr) := data["kind"]? | fail s!"opaqueInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let kind ←
    match kindStr with
    | "type" => pure .type
    | "ctor" => pure .ctor
    | "lift" => pure .lift
    | "ind" => pure .ind
    | _ => fail s!"unknown quot kind: {kindStr}"

  addConst name <| .quotInfo { name, levelParams, type, kind }

def parseInductInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["inductInfo"]? | fail s!"inductInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"inductInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"inductInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"inductInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"inductInfo invalid"
  let some (.num (numIndices : Nat)) := data["numIndices"]? | fail s!"inductInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"inductInfo invalid"
  let some (.arr ctorsIdxs) := data["ctors"]? | fail s!"inductInfo invalid"
  let some (.num (numNested : Nat)) := data["numNested"]? | fail s!"inductInfo invalid"
  let some (.bool isRec) := data["isRec"]? | fail s!"inductInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"inductInfo invalid"
  let some (.bool isReflexive) := data["isReflexive"]? | fail s!"inductInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let all ← getNameList allIdxs
  let ctors ← getNameList ctorsIdxs

  addConst name <| .inductInfo {
    name,
    levelParams,
    type,
    numParams,
    numIndices,
    all,
    ctors,
    numNested,
    isRec,
    isUnsafe,
    isReflexive,
  }

def parseCtorInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["ctorInfo"]? | fail s!"ctorInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"ctorInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"ctorInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"ctorInfo invalid"
  let some (.num (inductIdx : Nat)) := data["induct"]? | fail s!"ctorInfo invalid"
  let some (.num (cidx : Nat)) := data["cidx"]? | fail s!"ctorInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"ctorInfo invalid"
  let some (.num (numFields : Nat)) := data["numFields"]? | fail s!"ctorInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"ctorInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let induct ← getName inductIdx

  addConst name <| .ctorInfo {
    name,
    levelParams,
    type,
    induct,
    cidx,
    numParams,
    numFields,
    isUnsafe,
  }

def parseRecInfo (obj : Std.TreeMap.Raw String Json) : M Unit := do
  let some (.obj data) := obj["recInfo"]? | fail s!"recInfo invalid"
  let some (.num (nameIdx : Nat)) := data["name"]? | fail s!"recInfo invalid"
  let some (.arr levelParamsIdxs) := data["levelParams"]? | fail s!"recInfo invalid"
  let some (.num (typeIdx : Nat)) := data["type"]? | fail s!"recInfo invalid"
  let some (.arr allIdxs) := data["all"]? | fail s!"recInfo invalid"
  let some (.num (numParams : Nat)) := data["numParams"]? | fail s!"recInfo invalid"
  let some (.num (numIndices : Nat)) := data["numIndices"]? | fail s!"recInfo invalid"
  let some (.num (numMotives : Nat)) := data["numMotives"]? | fail s!"recInfo invalid"
  let some (.num (numMinors : Nat)) := data["numMinors"]? | fail s!"recInfo invalid"
  let some (.bool k) := data["k"]? | fail s!"recInfo invalid"
  let some (.arr rules) := data["rules"]? | fail s!"recInfo invalid"
  let some (.bool isUnsafe) := data["isUnsafe"]? | fail s!"recInfo invalid"

  let name ← getName nameIdx
  let levelParams ← getNameList levelParamsIdxs
  let type ← getExpr typeIdx
  let all ← getNameList allIdxs
  let rules ← rules.toList.mapM fun rule => do
    let .obj rule := rule | fail s!"recInfo invalid"
    let some (.num (ctorIdx : Nat)) := rule["ctor"]? | fail s!"recInfo invalid"
    let some (.num (nfields : Nat)) := rule["nfields"]? | fail s!"recInfo invalid"
    let some (.num (rhsIdx : Nat)) := rule["rhs"]? | fail s!"recInfo invalid"

    let ctor ← getName ctorIdx
    let rhs ← getExpr rhsIdx
    return { ctor, nfields, rhs }

  addConst name <| .recInfo {
    name,
    levelParams,
    type,
    all,
    numParams,
    numIndices,
    numMotives,
    numMinors,
    rules,
    k,
    isUnsafe,
  }

def parseItem : M Unit := do
  let obj ← parseJsonObj
  if obj.contains "str" then
    parseNameStr obj
  else if obj.contains "num" then
    parseNameNum obj
  else if obj.contains "succ" then
    parseLevelSucc obj
  else if obj.contains "max" then
    parseLevelMax obj
  else if obj.contains "imax" then
    parseLevelImax obj
  else if obj.contains "param" then
    parseLevelParam obj
  else if obj.contains "bvar" then
    parseExprBVar obj
  else if obj.contains "sort" then
    parseExprSort obj
  else if obj.contains "const" then
    parseExprConst obj
  else if obj.contains "app" then
    parseExprApp obj
  else if obj.contains "lam" then
    parseExprLam obj
  else if obj.contains "forallE" then
    parseExprForallE obj
  else if obj.contains "letE" then
    parseExprLetE obj
  else if obj.contains "proj" then
    parseExprProj obj
  else if obj.contains "natVal" then
    parseExprNatLit obj
  else if obj.contains "strVal" then
    parseExprStrLit obj
  else if obj.contains "mdata" then
    parseExprMdata obj
  else if obj.contains "axiomInfo" then
    parseAxiomInfo obj
  else if obj.contains "defnInfo" then
    parseDefnInfo obj
  else if obj.contains "thmInfo" then
    parseThmInfo obj
  else if obj.contains "opaqueInfo" then
    parseOpaqueInfo obj
  else if obj.contains "quotInfo" then
    parseQuotInfo obj
  else if obj.contains "inductInfo" then
    parseInductInfo obj
  else if obj.contains "ctorInfo" then
    parseCtorInfo obj
  else if obj.contains "recInfo" then
    parseRecInfo obj
  else
    fail s!"Unknown export object: {obj.keys}"
  ws


partial def parseItems : M Unit :=
  go
where
  go : M Unit := do
    if ← isEof (ι := Sigma String.Pos) then
      return ()
    else
      parseItem
      go

def parseMdata : M Unit := do
  discard <| parseJsonObj

def parseFile : M Unit := do
  parseMdata
  parseItems

end Parse

def parse (input : String) : Except String ExportedEnv := do
  let (_, state) ← Parse.M.run Parse.parseFile input
  let { constMap, constOrder, .. } := state
  return {
    constMap,
    constOrder,
  }

end Export
