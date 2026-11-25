import Lean
import Std.Data.HashMap.Basic
import Std.Sync.Channel
import Export
import Export.IndexSet

/-!
# Parallel exporter

Produces exactly the same bytes as the sequential exporter in `Export.lean`, using several cores.

1. A producer thread walks the constant dependency graph in the original order (the original
   `dumpConstant` control flow, minus the output) and, for each constant or inductive block, spawns
   one task per root expression and queues a `Block` in a bounded channel.
2. A worker task strips `mdata` from its root expression and walks it once, numbering the
   distinct nodes locally in first-visit post-order (`Root`).
3. The main thread takes blocks in order and merges each root into the global tables. A node is new
   if and only if the sequential exporter would have printed it, because a node seen before implies
   its whole subtree was seen before. Nodes are identified by `(tag, child indices)`, which is the
   equivalence of `Expr.eqv` (binder names and binder info are ignored), so no structural
   equality test is needed.
4. Output lines are built and compressed by worker tasks and written in order.

One case the sequential exporter handles in the middle of an expression is not reproducible here:
a `Nat` or `String` literal seen before `Nat` (or `Char.ofNat`/`String.ofList`) was exported.
It is detected, and the exporter stops with a message that names `--serial-walk`.
-/

open Lean
open Std (HashMap)

namespace ExportPar

open Export.IndexSet (getSlot setSlot homeSlot emptySlotFrom numSlots zeroSlots)

/-! ## A table of 4-word keys with dense indices -/

/-- Keys `(k0, k1, k2, k3)` numbered `0, 1, 2, …` in insertion order, 16 bytes per key. -/
structure NodeTable where
  chunks : Array ByteArray
  size : Nat
  slots : ByteArray

namespace NodeTable

def chunkBits : Nat := 18

def empty : NodeTable := ⟨#[], 0, zeroSlots 8⟩

instance : Inhabited NodeTable := ⟨⟨#[], 0, zeroSlots 8⟩⟩

@[inline] def word (chunks : @& Array ByteArray) (i k : Nat) : UInt32 :=
  (getSlot chunks[i >>> chunkBits]! (4 * (i &&& ((1 <<< chunkBits) - 1)) + k)).toUInt32

@[inline] def hashKey (k0 k1 k2 k3 : UInt32) : UInt64 :=
  let m := fun (h : UInt64) (x : UInt32) => (h ^^^ x.toUInt64) * 0x9E3779B97F4A7C15
  let h := m (m (m (m 0x84222325CBF29CE4 k0) k1) k2) k3
  h ^^^ (h >>> 32)

@[inline] def pushU32 (b : ByteArray) (v : UInt32) : ByteArray :=
  let b := b.push v.toUInt8
  let b := b.push (v >>> 8).toUInt8
  let b := b.push (v >>> 16).toUInt8
  b.push (v >>> 24).toUInt8

partial def findSlotFrom (t : @& NodeTable) (k0 k1 k2 k3 : UInt32) (mask i : Nat) : Nat :=
  let v := getSlot t.slots i
  if v == 0 then i
  else
    let j := v - 1
    if word t.chunks j 0 == k0 && word t.chunks j 1 == k1 && word t.chunks j 2 == k2 &&
        word t.chunks j 3 == k3 then i
    else findSlotFrom t k0 k1 k2 k3 mask ((i + 1) &&& mask)

/-- The index of the key, if present. -/
def find? (t : @& NodeTable) (k0 k1 k2 k3 : UInt32) : Option Nat :=
  let mask := numSlots t.slots - 1
  let v := getSlot t.slots (findSlotFrom t k0 k1 k2 k3 mask (homeSlot (hashKey k0 k1 k2 k3) mask))
  if v == 0 then none else some (v - 1)

def rebuild (chunks : @& Array ByteArray) (size n : Nat) : ByteArray := Id.run do
  let mut slots := zeroSlots n
  let mask := n - 1
  for i in [0:size] do
    let h := hashKey (word chunks i 0) (word chunks i 1) (word chunks i 2) (word chunks i 3)
    slots := setSlot slots (emptySlotFrom slots mask (homeSlot h mask)) (i + 1)
  return slots

/-- Adds a key (which must not be present) with index `t.size`. -/
def push (t : NodeTable) (k0 k1 k2 k3 : UInt32) : NodeTable :=
  let ⟨chunks, size, slots⟩ := t
  if size ≥ Export.IndexSet.maxSize then
    panic! "NodeTable.push: too many elements"
  else
    let n := numSlots slots
    let slots := if 2 * (size + 1) > n then rebuild chunks size (2 * n) else slots
    let mask := numSlots slots - 1
    let slots := setSlot slots (emptySlotFrom slots mask (homeSlot (hashKey k0 k1 k2 k3) mask)) (size + 1)
    let add := fun (b : ByteArray) => pushU32 (pushU32 (pushU32 (pushU32 b k0) k1) k2) k3
    let chunks :=
      if size &&& ((1 <<< chunkBits) - 1) == 0 then
        chunks.push (add (ByteArray.emptyWithCapacity (16 <<< chunkBits)))
      else
        chunks.modify (chunks.size - 1) add
    ⟨chunks, size + 1, slots⟩

end NodeTable

/-! ## Worker side: strip `mdata` and number the distinct nodes of one expression -/

/-- Same normalization as `removeMData` in `Export.lean`, as a pure function. -/
partial def strip (e : Expr) : StateM (HashMap Expr Expr) Expr := do
  if let some x := (← get)[e]? then
    return x
  let e' ← match e with
  | .mdata _ e' => strip e'
  | .fvar .. | .mvar .. => unreachable!
  | .bvar .. | .sort .. | .const .. | .lit _ => pure e
  | .app f a => do
    let f' ← strip f
    let a' ← strip a
    pure <| e.updateApp! f' a'
  | .lam _ d b _ => do
    let d' ← strip d
    let b' ← strip b
    pure <| e.updateLambdaE! d' b'
  | .letE _ d v b _ => do
    let d' ← strip d
    let v' ← strip v
    let b' ← strip b
    pure <| e.updateLet! d' v' b' false
  | .forallE _ d b _ => do
    let d' ← strip d
    let b' ← strip b
    pure <| e.updateForallE! d' b'
  | .proj _ _ e2 => do
    let e2' ← strip e2
    pure <| e.updateProj! e2'
  modify (·.insert e e')
  pure e'

/-- Node kinds. `pre` marks where the block of a binder or projection node starts. -/
def tBVar : UInt8 := 0
def tSort : UInt8 := 1
def tConst : UInt8 := 2
def tLit : UInt8 := 3
def tApp : UInt8 := 4
def tLam : UInt8 := 5
def tForall : UInt8 := 6
def tLet : UInt8 := 7
def tProj : UInt8 := 8
def tPre : UInt8 := 255

/-- One distinct node, children given as positions in the same array (always earlier ones).
For `tPre`, `a` is the position of the node it precedes. -/
structure Rec where
  tag : UInt8
  /-- The position where the first-visit block of this node starts. -/
  start : UInt32 := 0
  a : UInt32 := 0
  b : UInt32 := 0
  c : UInt32 := 0
  e : Expr := .bvar 0

instance : Inhabited Rec := ⟨{ tag := 0 }⟩

structure Root where
  recs : Array Rec
  rootPos : UInt32
  hasNat : Bool
  hasStr : Bool

instance : Inhabited Root := ⟨⟨#[], 0, false, false⟩⟩

structure W where
  recs : Array Rec := #[]
  seen : HashMap Expr UInt32 := {}
  hasNat : Bool := false
  hasStr : Bool := false

abbrev WM := StateM W

def pushRec (r : Rec) : WM UInt32 :=
  modifyGet fun w => (w.recs.size.toUInt32, { w with recs := w.recs.push r })

def setPre (pre p : UInt32) : WM Unit :=
  modify fun w => { w with recs := w.recs.modify pre.toNat fun r => { r with a := p } }

/-- First-visit post-order over distinct nodes, in the child order of the sequential exporter. -/
partial def walk (e : Expr) : WM UInt32 := do
  if let some p := (← get).seen[e]? then
    return p
  let st := (← get).recs.size.toUInt32
  let p ← match e with
    | .fvar .. | .mvar .. | .mdata .. => panic! "unexpected expression after normalization"
    | .bvar _ => pushRec { start := st, tag := tBVar, e := e }
    | .sort _ => pushRec { start := st, tag := tSort, e := e }
    | .const .. => pushRec { start := st, tag := tConst, e := e }
    | .lit l => do
      match l with
      | .natVal _ => modify fun w => { w with hasNat := true }
      | .strVal _ => modify fun w => { w with hasStr := true }
      pushRec { start := st, tag := tLit, e := e }
    | .app f a => do
      let pf ← walk f
      let pa ← walk a
      pushRec { start := st, tag := tApp, a := pf, b := pa, e := e }
    | .lam _ d b _ => do
      let pre ← pushRec { start := st, tag := tPre, e := e }
      let pd ← walk d
      let pb ← walk b
      let p ← pushRec { start := st, tag := tLam, a := pd, b := pb, e := e }
      setPre pre p
      pure p
    | .forallE _ d b _ => do
      let pre ← pushRec { start := st, tag := tPre, e := e }
      let pd ← walk d
      let pb ← walk b
      let p ← pushRec { start := st, tag := tForall, a := pd, b := pb, e := e }
      setPre pre p
      pure p
    | .letE _ d v b _ => do
      let pre ← pushRec { start := st, tag := tPre, e := e }
      let pd ← walk d
      let pv ← walk v
      let pb ← walk b
      let p ← pushRec { start := st, tag := tLet, a := pd, b := pv, c := pb, e := e }
      setPre pre p
      pure p
    | .proj _ _ s => do
      let pre ← pushRec { start := st, tag := tPre, e := e }
      let ps ← walk s
      let p ← pushRec { start := st, tag := tProj, a := ps, e := e }
      setPre pre p
      pure p
  modify fun w => { w with seen := w.seen.insert e p }
  return p

def buildRoot (e : Expr) : Root :=
  let (e', _) := (strip e).run {}
  let (p, w) := (walk e').run {}
  { recs := w.recs, rootPos := p, hasNat := w.hasNat, hasStr := w.hasStr }

/-! ## Output -/

/-- One output line. `expr` carries what is needed to print an expression node. -/
inductive Entry where
  | json (j : Json)
  /-- `idx`, name index `n`, child indices `a b c`, level indices `us` (constants), the node. -/
  | expr (idx n a b c : Nat) (us : Array Nat) (e : Expr)

def exprJson (e : Expr) (n a b c : Nat) (us : Array Nat) : Json :=
  match e with
  | .bvar i => .mkObj [("bvar", i)]
  | .lit (.natVal i) => .mkObj [("natVal", s!"{i}")]
  | .lit (.strVal s) => .mkObj [("strVal", s)]
  | .sort _ => .mkObj [("sort", a)]
  | .const _ _ => .mkObj [
      ("const", .mkObj [
        ("name", n),
        ("us", us.toList.toJson)
      ])
    ]
  | .app .. => .mkObj [
      ("app", .mkObj [
        ("fn", a),
        ("arg", b)
      ])
    ]
  | .lam _ _ _ bi => .mkObj [
      ("lam", .mkObj [
        ("name", n),
        ("type", a),
        ("body", b),
        ("binderInfo", bi.toJson)
      ])
    ]
  | .forallE _ _ _ bi => .mkObj [
      ("forallE", .mkObj [
        ("name", n),
        ("type", a),
        ("body", b),
        ("binderInfo", bi.toJson)
      ])
    ]
  | .letE _ _ _ _ nondep => .mkObj [
      ("letE", .mkObj [
        ("name", n),
        ("type", a),
        ("value", b),
        ("body", c),
        ("nondep", nondep)
      ])
    ]
  | .proj _ i _ => .mkObj [
      ("proj", .mkObj [
        ("typeName", n),
        ("idx", i),
        ("struct", a)
      ])
    ]
  | .fvar .. | .mvar .. | .mdata .. => unreachable!

def formatEntry (en : Entry) : String :=
  match en with
  | .json j => j.compress
  | .expr idx n a b c us e => ((exprJson e n a b c us).setObjVal! "ie" idx).compress

def formatBatchP (b : Array Entry) : String :=
  b.foldl (init := "") fun acc en => (acc.append (formatEntry en)).push '\n'

/-! ## Producer side: the constant graph in the original order -/

/-- What the main thread prints for one constant (or inductive block, or the Quot package). -/
inductive Body where
  | axm (val : AxiomVal)
  | defn (val : DefinitionVal)
  | opaq (val : OpaqueVal)
  | thm (val : TheoremVal)
  | quot (vals : Array QuotVal)
  | induct (indVals : Array InductiveVal) (ctorVals : Array ConstructorVal)
      (recVals : Array RecursorVal)

/-- A `Body` with one task per expression it prints, in printing order. If its expressions contain
a `Nat` (`String`) literal while the constants the sequential exporter exports at the first such
literal are not exported yet, `natDeps` (`strDeps`) are their blocks. The merge runs them at that
literal. -/
structure Block where
  body : Body
  roots : Array (Task Root)
  natDeps : Option (Array Block) := none
  strDeps : Option (Array Block) := none

instance : Inhabited Block := ⟨⟨.quot #[], #[], none, none⟩⟩

structure AEnv where
  env : Environment
  exportUnsafe : Bool
  ignoreMissing : Bool
  recursorMap : NameMap NameSet
  send : Block → IO Unit

abbrev MA := ReaderT AEnv <| StateT NameHashSet IO

def spawnRoot (e : Expr) : Task Root := Task.spawn fun _ => buildRoot e

def hasNatLit (e : Expr) : Bool :=
  (e.find? fun x => match x with | .lit (.natVal _) => true | _ => false).isSome

def hasStrLit (e : Expr) : Bool :=
  (e.find? fun x => match x with | .lit (.strVal _) => true | _ => false).isSome

mutual

partial def discover (c : Name) : MA Unit := do
  let ctx ← read
  let some declar := ctx.env.find? c
    | if ctx.ignoreMissing then return else panic! s!"Constant {c} not found in environment."
  if ((declar.isUnsafe || declar.isPartial) && !ctx.exportUnsafe) || (← get).contains c then
    return
  modify (·.insert c)
  match declar with
  | .axiomInfo val => do
    deps val.type
    mk (.axm val) #[val.type]
  | .defnInfo val => do
    deps val.type
    deps val.value
    mk (.defn val) #[val.type, val.value]
  | .opaqueInfo val => do
    deps val.type
    deps val.value
    mk (.opaq val) #[val.type, val.value]
  | .thmInfo val => do
    deps val.type
    deps val.value
    mk (.thm val) #[val.type, val.value]
  | .quotInfo _ => do
    discover ``Eq
    let mut vals := #[]
    for c in [`Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      let some (.quotInfo val) := ctx.env.find? c
        | if ctx.ignoreMissing then break else panic! s!"Constant {c} not found in environment."
      modify (·.insert c)
      vals := vals.push val
    mk (.quot vals) (vals.map (·.type))
  | .inductInfo baseIndVal => do
    let mut indVals := #[]
    let mut ctorVals := #[]
    let mut recursorNames := NameSet.empty
    for indName in baseIndVal.all do
      let val := (ctx.env.find? indName |>.get!).inductiveVal!
      assert! ((!val.isUnsafe) || ctx.exportUnsafe)
      indVals := indVals.push val
      for ctor in val.ctors do
        match (ctx.env.find? ctor |>.get!) with
        | .ctorInfo ctorVal =>
          assert! ((!ctorVal.isUnsafe) || ctx.exportUnsafe)
          ctorVals := ctorVals.push ctorVal
        | _ => panic! "Expected a `ConstantInfo.ctorInfo`."
      modify (·.insert indName)
      deps val.type
      if let .some names := ctx.recursorMap.get? baseIndVal.name
      then recursorNames := recursorNames.union names
      else assert! ctorVals.size == 0
    for ctorVal in ctorVals do
      modify (·.insert ctorVal.name)
      deps ctorVal.type
    let mut recursorVals := #[]
    for recursorName in recursorNames do
      match (ctx.env.find? recursorName |>.get!) with
      | .recInfo recVal =>
        assert! ((!recVal.isUnsafe) || ctx.exportUnsafe)
        recursorVals := recursorVals.push recVal
      | _ => panic! "expected a `constantinfo.recinfo`."
    for recursorVal in recursorVals do
      modify (·.insert recursorVal.name)
      deps recursorVal.type
    for recursorVal in recursorVals do
      for rule in recursorVal.rules do
        deps rule.rhs
    -- The expressions in the order the main thread prints them.
    let mut es := #[]
    for v in indVals do es := es.push v.type
    for v in ctorVals do es := es.push v.type
    for v in recursorVals do
      es := es.push v.type
      for rule in v.rules do es := es.push rule.rhs
    mk (.induct indVals ctorVals recursorVals) es
  | .ctorInfo val => discover val.induct
  | .recInfo val =>
    for indName in val.all do
      discover indName
where
  deps (e : Expr) : MA Unit := do
    for c in e.getUsedConstants do
      discover c
  /-- Queue a block. The sequential exporter exports `Nat`, or `Char.ofNat` and `String.ofList`,
  at the first literal it prints, if they were not exported yet. -/
  mk (body : Body) (es : Array Expr) : MA Unit := do
    let ctx ← read
    let seen ← get
    let need (n : Name) := !seen.contains n && (ctx.env.find? n).isSome
    let mut natDeps := none
    let mut strDeps := none
    if need ``Nat && es.any hasNatLit then
      natDeps := some (← collect (discover ``Nat))
    if (need ``Char.ofNat || need ``String.ofList) && es.any hasStrLit then
      strDeps := some (← collect (do
        let seen ← get
        if !seen.contains ``Char.ofNat && (ctx.env.find? ``Char.ofNat).isSome then
          discover ``Char.ofNat
        let seen ← get
        if !seen.contains ``String.ofList && (ctx.env.find? ``String.ofList).isSome then
          discover ``String.ofList))
    ctx.send { body, roots := es.map spawnRoot, natDeps, strDeps }
  /-- Run `act`, returning the blocks it produces instead of queueing them. -/
  collect (act : MA Unit) : MA (Array Block) := do
    let ctx ← read
    let acc ← IO.mkRef (#[] : Array Block)
    let st ← get
    let ((), st') ← (act.run { ctx with send := fun b => acc.modify (·.push b) }).run st
    set st'
    acc.get

end

/-! ## Main thread: merge and print -/

structure G where
  names : Export.IndexSet Name := (Export.IndexSet.empty).push .anonymous
  levels : Export.IndexSet Level := (Export.IndexSet.empty).push .zero
  exprs : NodeTable := NodeTable.empty
  litIds : HashMap Literal Nat := {}
  levelLists : HashMap (List Nat) Nat := {}
  pending : Array Entry := #[]
  inflight : Array (Task String) := #[]
  rootQ : Array (Task Root) := #[]
  rootI : Nat := 0
  natTrig : Option (Array Block) := none
  strTrig : Option (Array Block) := none

abbrev MB := StateT G IO

def batchSize : Nat := 4096
def maxInflight : Nat := 64

def writeOldestG : MB Unit := do
  let g ← get
  if h : 0 < g.inflight.size then
    let t := g.inflight[0]
    set { g with inflight := g.inflight.eraseIdx 0 }
    (← IO.getStdout).putStr t.get

def spawnPendingG : MB Unit := do
  let g ← get
  let b := g.pending
  if b.isEmpty then return
  set { g with pending := #[], inflight := g.inflight.push (Task.spawn fun _ => formatBatchP b) }
  while (← get).inflight.size > maxInflight do
    writeOldestG

def emitE (en : Entry) : MB Unit := do
  modify fun g => { g with pending := g.pending.push en }
  if (← get).pending.size ≥ batchSize then spawnPendingG

def finishOutputG : MB Unit := do
  spawnPendingG
  while !(← get).inflight.isEmpty do
    writeOldestG

def tooMany (what : String) : IO α :=
  throw <| .userError s!"cannot export more than {Export.IndexSet.maxSize} distinct {what}"

partial def dumpNameG (n : Name) : MB Nat := do
  if let some idx := (← get).names.find? n then
    return idx
  let j ← match n with
    | .anonymous => unreachable!
    | .str n s => do
      pure <| Json.mkObj [
        ("str", .mkObj [
          ("pre", ← dumpNameG n),
          ("str", s)
        ])
      ]
    | .num n i => do
      pure <| Json.mkObj [
        ("num", .mkObj [
          ("pre", ← dumpNameG n),
          ("i", i)
        ])
      ]
  let idx := (← get).names.size
  if idx ≥ Export.IndexSet.maxSize then tooMany "names"
  emitE (.json (j.setObjVal! "in" idx))
  modify fun g => { g with names := g.names.push n }
  return idx

partial def dumpLevelG (l : Level) : MB Nat := do
  if let some idx := (← get).levels.find? l then
    return idx
  let j ← match l with
    | .zero | .mvar _ => unreachable!
    | .succ l => do pure <| Json.mkObj [("succ", ← dumpLevelG l)]
    | .max l1 l2 => do pure <| Json.mkObj [("max", Json.arr #[← dumpLevelG l1, ← dumpLevelG l2])]
    | .imax l1 l2 => do pure <| Json.mkObj [("imax", Json.arr #[← dumpLevelG l1, ← dumpLevelG l2])]
    | .param n => do pure <| Json.mkObj [("param", ← dumpNameG n)]
  let idx := (← get).levels.size
  if idx ≥ Export.IndexSet.maxSize then tooMany "levels"
  emitE (.json (j.setObjVal! "il" idx))
  modify fun g => { g with levels := g.levels.push l }
  return idx

def dumpUparamsG (uparams : List Name) : MB Json := do
  let nameIdxs ← uparams.mapM dumpNameG
  let _ ← (uparams.map (Level.param)).mapM dumpLevelG
  pure nameIdxs.toJson

def dumpNamesG (uparams : List Name) : MB Json := do
  let nameIdxs ← uparams.mapM dumpNameG
  return nameIdxs.toJson

def toU32 (n : Nat) : UInt32 :=
  if n < 2 ^ 32 then n.toUInt32 else panic! "index does not fit in 32 bits"

def isComposite (t : UInt8) : Bool :=
  t == tApp || t == tLam || t == tForall || t == tLet || t == tProj

def keyOf (e : Expr) (a b c : UInt32) (n : Nat) (lid : Nat) : UInt32 × UInt32 × UInt32 × UInt32 :=
  match e with
  | .bvar i => (0, toU32 i, 0, 0)
  | .sort _ => (1, a, 0, 0)
  | .const .. => (2, toU32 n, toU32 lid, 0)
  | .lit _ => (3, toU32 lid, 0, 0)
  | .app .. => (4, a, b, 0)
  | .lam .. => (5, a, b, 0)
  | .forallE .. => (6, a, b, 0)
  | .letE .. => (7, a, b, c)
  | .proj _ i _ => (8, toU32 n, toU32 i, a)
  | _ => (0, 0, 0, 0)

/-- For the nodes at positions `start ≤ p < cnt`: `index + 1` if the node is already known, `0` if
it is new. Nodes before `start` were handled already; `gidx` holds their indices. A node whose
first-visit block started before `start` encloses `start`, so it stays new. -/
def presence (g : G) (recs : Array Rec) (start : Nat) (gidx : Array UInt32)
    (pres : Array UInt32) : Array UInt32 := Id.run do
  let cnt := recs.size
  let mut pres := pres
  for p in [start:cnt] do
    let rc := recs[p]!
    let known (c : UInt32) : UInt32 :=
      if c.toNat < start then gidx[c.toNat]! + 1 else pres[c.toNat]!
    let v : UInt32 :=
      if rc.tag == tPre || (start > 0 && p > start && rc.start.toNat ≤ start) then 0
      else
        let pa := if isComposite rc.tag then known rc.a else 1
        let pb := if rc.tag == tApp || rc.tag == tLam || rc.tag == tForall || rc.tag == tLet then known rc.b else 1
        let pc := if rc.tag == tLet then known rc.c else 1
        if pa == 0 || pb == 0 || pc == 0 then 0
        else
          let found : Option Nat :=
            match rc.e with
            | .bvar i => g.exprs.find? 0 (toU32 i) 0 0
            | .sort l => (g.levels.find? l).bind fun li => g.exprs.find? 1 (toU32 li) 0 0
            | .const n us =>
              (g.names.find? n).bind fun ni =>
                (us.mapM g.levels.find?).bind fun lis => (g.levelLists[lis]?).bind fun lid =>
                  g.exprs.find? 2 (toU32 ni) (toU32 lid) 0
            | .lit l => (g.litIds[l]?).bind fun id => g.exprs.find? 3 (toU32 id) 0 0
            | .app .. => g.exprs.find? 4 (pa - 1) (pb - 1) 0
            | .lam .. => g.exprs.find? 5 (pa - 1) (pb - 1) 0
            | .forallE .. => g.exprs.find? 6 (pa - 1) (pb - 1) 0
            | .letE .. => g.exprs.find? 7 (pa - 1) (pb - 1) (pc - 1)
            | .proj s i _ => (g.names.find? s).bind fun ni => g.exprs.find? 8 (toU32 ni) (toU32 i) (pa - 1)
            | _ => none
          match found with
          | some idx => (toU32 idx) + 1
          | none => 0
    if p < pres.size then pres := pres.set! p v else pres := pres.push v
  return pres

mutual

/-- Merge one root into the tables, printing what is new, and return the root's index. -/
partial def mergeRoot (r : Root) : MB Nat := do
  let recs := r.recs
  let cnt := recs.size
  -- Pass 1: which nodes are already known?
  let mut pres : Array UInt32 := presence (← get) recs 0 #[] #[]
  -- Pass 2: print the new nodes, with the names and levels they bring, in the original order.
  let mut gidx : Array UInt32 := Array.emptyWithCapacity cnt
  for p in [0:cnt] do
    let rc := recs[p]!
    if rc.tag == tPre then
      if pres[rc.a.toNat]! == 0 then
        match recs[rc.a.toNat]!.e with
        | .lam nm .. | .forallE nm .. | .letE nm .. => discard <| dumpNameG nm
        | .proj s .. => discard <| dumpNameG s
        | _ => pure ()
      gidx := gidx.push 0
    else if pres[p]! != 0 then
      gidx := gidx.push (pres[p]! - 1)
    else
      -- The first new literal makes the sequential exporter export some constants first.
      if rc.tag == tLit then
        let trig ← match rc.e with
          | .lit (.natVal _) => modifyGet fun g => (g.natTrig, { g with natTrig := none })
          | _ => modifyGet fun g => (g.strTrig, { g with strTrig := none })
        if let some bs := trig then
          let saved := (← get)
          let (q, i, nt, st) := (saved.rootQ, saved.rootI, saved.natTrig, saved.strTrig)
          for b in bs do runBlock b
          modify fun g => { g with rootQ := q, rootI := i, natTrig := nt, strTrig := st }
          pres := presence (← get) recs p gidx pres
          -- This node stays new, as for the sequential exporter, which does not look again.
          pres := pres.set! p 0
      let ga := if isComposite rc.tag then gidx[rc.a.toNat]! else 0
      let gb := if rc.tag == tApp || rc.tag == tLam || rc.tag == tForall || rc.tag == tLet then gidx[rc.b.toNat]! else 0
      let gc := if rc.tag == tLet then gidx[rc.c.toNat]! else 0
      let mut ni : Nat := 0
      let mut lid : Nat := 0
      let mut us : Array Nat := #[]
      let mut ga := ga
      match rc.e with
      | .sort l => ga := toU32 (← dumpLevelG l)
      | .const n ls =>
        ni ← dumpNameG n
        for l in ls do us := us.push (← dumpLevelG l)
        if let some id := (← get).levelLists[us.toList]? then lid := id
        else
          lid := (← get).levelLists.size
          modify fun g => { g with levelLists := g.levelLists.insert us.toList lid }
      | .lit l =>
        if let some id := (← get).litIds[l]? then lid := id
        else
          lid := (← get).litIds.size
          modify fun g => { g with litIds := g.litIds.insert l lid }
      | .lam nm .. | .forallE nm .. | .letE nm .. => ni ← dumpNameG nm
      | .proj s .. => ni ← dumpNameG s
      | _ => pure ()
      let (k0, k1, k2, k3) := keyOf rc.e ga gb gc ni lid
      let idx := (← get).exprs.size
      if idx ≥ Export.IndexSet.maxSize then tooMany "expressions"
      modify fun g => { g with exprs := g.exprs.push k0 k1 k2 k3 }
      emitE (.expr idx ni ga.toNat gb.toNat gc.toNat us rc.e)
      gidx := gidx.push idx.toUInt32
  return gidx[r.rootPos.toNat]!.toNat

/-- The next expression of the current block, already numbered and printed. -/
partial def dumpExprG (_e : Expr) : MB Nat := do
  let t := (← get).rootQ[(← get).rootI]!
  modify fun g => { g with rootI := g.rootI + 1 }
  mergeRoot t.get

partial def dumpRecRuleG (rule : RecursorRule) : MB Json := do
  return Json.mkObj [
    ("ctor", ← dumpNameG rule.ctor),
    ("nfields", rule.nfields),
    ("rhs", ← dumpExprG rule.rhs),
  ]

partial def runBlock (b : Block) : MB Unit := do
  modify fun g => { g with rootQ := b.roots, rootI := 0, natTrig := b.natDeps, strTrig := b.strDeps }
  match b.body with
  | .axm val =>
    dumpObjG [
      ("axiom", Json.mkObj [
        ("name", ← dumpNameG val.name),
        ("levelParams", ← dumpUparamsG val.levelParams),
        ("type", ← dumpExprG val.type),
        ("isUnsafe", val.isUnsafe)
      ])
    ]
  | .defn val =>
    dumpObjG [
      ("def", Json.mkObj [
        ("name", ← dumpNameG val.name),
        ("levelParams", ← dumpUparamsG val.levelParams),
        ("type", ← dumpExprG val.type),
        ("value", ← dumpExprG val.value),
        ("hints", val.hints.toJson),
        ("safety", val.safety.toJson),
        ("all", ← dumpNamesG val.all)
      ])
    ]
  | .opaq val =>
    dumpObjG [
      ("opaque", Json.mkObj [
        ("name", ← dumpNameG val.name),
        ("levelParams", ← dumpUparamsG val.levelParams),
        ("type", ← dumpExprG val.type),
        ("value", ← dumpExprG val.value),
        ("all", ← dumpNamesG val.all),
        ("isUnsafe", val.isUnsafe)
      ])
    ]
  | .thm val =>
    dumpObjG [
      ("thm", Json.mkObj [
        ("name", ← dumpNameG val.name),
        ("levelParams", ← dumpUparamsG val.levelParams),
        ("type", ← dumpExprG val.type),
        ("value", ← dumpExprG val.value),
        ("all", ← dumpNamesG val.all)
      ])
    ]
  | .quot vals =>
    for val in vals do
      dumpObjG [
        ("quot", .mkObj [
          ("name", ← dumpNameG val.name),
          ("levelParams", ← dumpUparamsG val.levelParams),
          ("type", ← dumpExprG val.type),
          ("kind", val.kind.toJson)
        ])
      ]
  | .induct indVals ctorVals recursorVals =>
    let inductiveValsJson ← indVals.mapM <| fun indVal => do
      pure <| Json.mkObj [
          ("name", ← dumpNameG indVal.name),
          ("levelParams", ← dumpUparamsG indVal.levelParams),
          ("type", ← dumpExprG indVal.type),
          ("numParams", indVal.numParams),
          ("numIndices", indVal.numIndices),
          ("all", ← dumpNamesG indVal.all),
          ("ctors", ← dumpNamesG indVal.ctors),
          ("numNested", indVal.numNested),
          ("isRec", indVal.isRec),
          ("isReflexive", indVal.isReflexive),
          ("isUnsafe", indVal.isUnsafe),
      ]
    let ctorValsJson ← ctorVals.mapM <| fun ctorVal => do
      pure <| Json.mkObj [
          ("name", ← dumpNameG ctorVal.name),
          ("levelParams", ← dumpUparamsG ctorVal.levelParams),
          ("type", ← dumpExprG ctorVal.type),
          ("induct", ← dumpNameG ctorVal.induct),
          ("cidx", ctorVal.cidx),
          ("numParams", ctorVal.numParams),
          ("numFields", ctorVal.numFields),
          ("isUnsafe", ctorVal.isUnsafe)
      ]
    let recursorValsJson ← recursorVals.mapM <| fun recursorVal => do
      pure <| Json.mkObj [
          ("name", ← dumpNameG recursorVal.name),
          ("levelParams", ← dumpUparamsG recursorVal.levelParams),
          ("type", ← dumpExprG recursorVal.type),
          ("all", ← dumpNamesG recursorVal.all),
          ("numParams", recursorVal.numParams),
          ("numIndices", recursorVal.numIndices),
          ("numMotives", recursorVal.numMotives),
          ("numMinors", recursorVal.numMinors),
          ("rules", (← recursorVal.rules.mapM dumpRecRuleG).toJson),
          ("k", recursorVal.k),
          ("isUnsafe", recursorVal.isUnsafe),
      ]
    dumpObjG [
      ("inductive", Json.mkObj [
        ("types", inductiveValsJson.toJson),
        ("ctors", ctorValsJson.toJson),
        ("recs", recursorValsJson.toJson),
      ])
    ]
  if (← get).natTrig.isSome || (← get).strTrig.isSome then
    throw <| .userError "internal error: a literal trigger was not used; rerun with --serial-walk"
where
  dumpObjG (fields : List (String × Json)) : MB Unit :=
    emitE (.json (Json.mkObj fields))

end

/-- Export `constants`, using worker threads. Output is identical to the sequential exporter. -/
def run (env : Environment) (cliOptions : List String) (constants : List Name)
    (window : Nat := 512) : IO Unit := do
  let mut recursorMap : NameMap NameSet := {}
  for (_, constInfo) in env.constants do
    if let .recInfo recVal := constInfo then
      for indName in recVal.all do
        recursorMap := recursorMap.alter indName <|
          fun
          | none => some <| NameSet.empty.insert recVal.name
          | some recNames => some <| recNames.insert recVal.name
  let ch ← Std.CloseableChannel.Sync.new (some window)
  let sent ← IO.mkRef 0
  let trace := cliOptions.any (· == "--trace")
  let send : Block → IO Unit := fun b => do
    (ch.send b).toIO fun _ => IO.userError "export stopped"
    let n ← sent.modifyGet fun n => (n + 1, n + 1)
    if trace && n % 1000 == 0 then IO.eprintln s!"[producer] sent {n} blocks"
  let ctx : AEnv := {
    env, send, recursorMap
    exportUnsafe := cliOptions.any (· == "--export-unsafe")
    ignoreMissing := cliOptions.any (· == "--ignore-missing") }
  let producer ← IO.asTask (prio := .dedicated) do
    try
      let _ ← (do for c in constants do discover c : MA Unit).run ctx |>.run {}
    finally
      discard <| (ch.close).toBaseIO
  let consumer : IO Unit := do
    let _ ← (do
      emitE (.json exportMetadata)
      let mut n := 0
      repeat
        match ← ch.recv with
        | none => break
        | some b =>
          runBlock b
          n := n + 1
          if trace && n % 1000 == 0 then IO.eprintln s!"[consumer] merged {n} blocks"
      finishOutputG : MB Unit).run {}
  try consumer
  finally discard <| (ch.close).toBaseIO
  match producer.get with
  | .ok _ => pure ()
  | .error e => throw e

end ExportPar
