import Export
import Export.Parse
open Lean

def run (act : M α) : MetaM Unit := do
  let env ← getEnv
  let _ ← M.run env (do initState env; act)

def runEmpty (act : M α) : MetaM Unit := do
  let env ← Lean.mkEmptyEnvironment
  let _ ← M.run env (do initState env; act)

/--
info: {"str":{"str":"foo","pre":0},"in":1}
{"str":{"str":"bla","pre":1},"in":2}
{"num":{"pre":2,"i":1},"in":3}
{"str":{"str":"boo","pre":3},"in":4}
-/
#guard_msgs in
#eval run <| dumpName (`foo.bla |>.num 1 |>.str "boo")

/-- info: {"str":{"str":"\npq\n  \nrs\u0009\r\nuv\n\n","pre":0},"in":1} -/
#guard_msgs in
#eval run <| dumpName (Name.str Name.anonymous "\npq\n  \nrs\t\r\nuv\n\n")

/--
info: {"succ":0,"il":1}
{"succ":1,"il":2}
{"str":{"str":"l1","pre":0},"in":1}
{"param":1,"il":3}
{"max":[2,3],"il":4}
{"str":{"str":"l2","pre":0},"in":2}
{"param":2,"il":5}
{"imax":[4,5],"il":6}
-/
#guard_msgs in
#eval run <| dumpLevel (.imax (.max (.succ (.succ .zero)) (.param `l1)) (.param `l2))

/--
info: {"str":{"str":"A","pre":0},"in":1}
{"succ":0,"il":1}
{"sort":1,"ie":0}
{"str":{"str":"a","pre":0},"in":2}
{"ie":1,"bvar":0}
{"lam":{"type":1,"name":2,"body":1,"binderInfo":"default"},"ie":2}
{"lam":{"type":0,"name":1,"body":2,"binderInfo":"implicit"},"ie":3}
-/
#guard_msgs in
#eval run <| dumpExpr (.lam `A (.sort (.succ .zero)) (.lam `a (.bvar 0) (.bvar 0) .default) .implicit)

/--
info: {"str":{"str":"x","pre":0},"in":1}
{"str":{"str":"Nat","pre":0},"in":2}
{"ie":0,"const":{"us":[],"name":2}}
{"str":{"str":"zero","pre":2},"in":3}
{"ie":1,"const":{"us":[],"name":3}}
{"ie":2,"bvar":0}
{"letE":{"value":1,"type":0,"nondep":false,"name":1,"body":2},"ie":3}
-/
#guard_msgs in
#eval run <| dumpExpr (.letE `x (.const `Nat []) (.const `Nat.zero []) (.bvar 0) false)

/--
info: {"str":{"str":"Prod","pre":0},"in":1}
{"ie":0,"bvar":0}
{"proj":{"typeName":1,"struct":0,"idx":1},"ie":1}
-/
#guard_msgs in
#eval run <| dumpExpr (.proj `Prod 1 (.bvar 0))

/-- info: {"natVal":"100000000000000023456789","ie":0} -/
#guard_msgs in
#eval runEmpty <| dumpExpr (.lit (.natVal 100000000000000023456789))

/--
info: {"str":{"str":"Nat","pre":0},"in":1}
{"succ":0,"il":1}
{"sort":1,"ie":0}
{"str":{"str":"zero","pre":1},"in":2}
{"str":{"str":"succ","pre":1},"in":3}
{"ie":1,"const":{"us":[],"name":1}}
{"str":{"str":"n","pre":0},"in":4}
{"ie":2,"forallE":{"type":1,"name":4,"body":1,"binderInfo":"default"}}
{"str":{"str":"rec","pre":1},"in":5}
{"str":{"str":"u","pre":0},"in":6}
{"param":6,"il":2}
{"str":{"str":"motive","pre":0},"in":7}
{"str":{"str":"t","pre":0},"in":8}
{"sort":2,"ie":3}
{"ie":4,"forallE":{"type":1,"name":8,"body":3,"binderInfo":"default"}}
{"str":{"str":"zero","pre":0},"in":9}
{"ie":5,"bvar":0}
{"ie":6,"const":{"us":[],"name":2}}
{"ie":7,"app":{"fn":5,"arg":6}}
{"str":{"str":"succ","pre":0},"in":10}
{"str":{"str":"n_ih","pre":0},"in":11}
{"ie":8,"bvar":2}
{"ie":9,"app":{"fn":8,"arg":5}}
{"ie":10,"bvar":3}
{"ie":11,"const":{"us":[],"name":3}}
{"ie":12,"bvar":1}
{"ie":13,"app":{"fn":11,"arg":12}}
{"ie":14,"app":{"fn":10,"arg":13}}
{"ie":15,"forallE":{"type":9,"name":11,"body":14,"binderInfo":"default"}}
{"ie":16,"forallE":{"type":1,"name":4,"body":15,"binderInfo":"default"}}
{"ie":17,"app":{"fn":10,"arg":5}}
{"ie":18,"forallE":{"type":1,"name":8,"body":17,"binderInfo":"default"}}
{"ie":19,"forallE":{"type":16,"name":10,"body":18,"binderInfo":"default"}}
{"ie":20,"forallE":{"type":7,"name":9,"body":19,"binderInfo":"default"}}
{"ie":21,"forallE":{"type":4,"name":7,"body":20,"binderInfo":"implicit"}}
{"lam":{"type":16,"name":10,"body":12,"binderInfo":"default"},"ie":22}
{"lam":{"type":7,"name":9,"body":22,"binderInfo":"default"},"ie":23}
{"lam":{"type":4,"name":7,"body":23,"binderInfo":"default"},"ie":24}
{"ie":25,"app":{"fn":12,"arg":5}}
{"ie":26,"const":{"us":[2],"name":5}}
{"ie":27,"app":{"fn":26,"arg":10}}
{"ie":28,"app":{"fn":27,"arg":8}}
{"ie":29,"app":{"fn":28,"arg":12}}
{"ie":30,"app":{"fn":29,"arg":5}}
{"ie":31,"app":{"fn":25,"arg":30}}
{"lam":{"type":1,"name":4,"body":31,"binderInfo":"default"},"ie":32}
{"lam":{"type":16,"name":10,"body":32,"binderInfo":"default"},"ie":33}
{"lam":{"type":7,"name":9,"body":33,"binderInfo":"default"},"ie":34}
{"lam":{"type":4,"name":7,"body":34,"binderInfo":"default"},"ie":35}
{"inductive":{"types":[{"type":0,"numParams":0,"numNested":0,"numIndices":0,"name":1,"levelParams":[],"isUnsafe":false,"isReflexive":false,"isRec":true,"ctors":[2,3],"all":[1]}],"recs":[{"type":21,"rules":[{"rhs":24,"nfields":0,"ctor":2},{"rhs":35,"nfields":1,"ctor":3}],"numParams":0,"numMotives":1,"numMinors":2,"numIndices":0,"name":5,"levelParams":[6],"k":false,"isUnsafe":false,"all":[1]}],"ctors":[{"type":1,"numParams":0,"numFields":0,"name":2,"levelParams":[],"isUnsafe":false,"induct":1,"cidx":0},{"type":2,"numParams":0,"numFields":1,"name":3,"levelParams":[],"isUnsafe":false,"induct":1,"cidx":1}]}}
{"natVal":"100000000000000023456789","ie":36}
-/
#guard_msgs in
#eval run <| dumpExpr (.lit (.natVal 100000000000000023456789))

/-- info: {"strVal":"hi","ie":0} -/
#guard_msgs in
#eval runEmpty <| dumpExpr (.lit (.strVal "hi"))

/-- info: {"strVal":"\r\rh\ni\u0009\u0009","ie":0} -/
#guard_msgs in
#eval runEmpty <| dumpExpr (.lit (.strVal "\r\rh
i\t\t"))

/--
info: {"strVal":"اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр","ie":0}
-/
#guard_msgs in
#eval runEmpty <| dumpExpr
  (.lit (.strVal "اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр"))

/--
info: {"str":{"str":"id","pre":0},"in":1}
{"str":{"str":"u","pre":0},"in":2}
{"param":2,"il":1}
{"str":{"str":"α","pre":0},"in":3}
{"sort":1,"ie":0}
{"str":{"str":"a","pre":0},"in":4}
{"ie":1,"bvar":0}
{"ie":2,"bvar":1}
{"ie":3,"forallE":{"type":1,"name":4,"body":2,"binderInfo":"default"}}
{"ie":4,"forallE":{"type":0,"name":3,"body":3,"binderInfo":"implicit"}}
{"lam":{"type":1,"name":4,"body":1,"binderInfo":"default"},"ie":5}
{"lam":{"type":0,"name":3,"body":5,"binderInfo":"implicit"},"ie":6}
{"def":{"value":6,"type":4,"safety":"safe","name":1,"levelParams":[2],"hints":{"regular":1},"all":[1]}}
-/
#guard_msgs in
#eval run <| do
  initState (← read).env
  dumpConstant `id

/--
info: {"str":{"str":"List","pre":0},"in":1}
{"str":{"str":"u","pre":0},"in":2}
{"param":2,"il":1}
{"str":{"str":"α","pre":0},"in":3}
{"succ":1,"il":2}
{"sort":2,"ie":0}
{"ie":1,"forallE":{"type":0,"name":3,"body":0,"binderInfo":"default"}}
{"str":{"str":"nil","pre":1},"in":4}
{"str":{"str":"cons","pre":1},"in":5}
{"ie":2,"const":{"us":[1],"name":1}}
{"ie":3,"bvar":0}
{"ie":4,"app":{"fn":2,"arg":3}}
{"ie":5,"forallE":{"type":0,"name":3,"body":4,"binderInfo":"implicit"}}
{"str":{"str":"head","pre":0},"in":6}
{"str":{"str":"tail","pre":0},"in":7}
{"ie":6,"bvar":1}
{"ie":7,"app":{"fn":2,"arg":6}}
{"ie":8,"bvar":2}
{"ie":9,"app":{"fn":2,"arg":8}}
{"ie":10,"forallE":{"type":7,"name":7,"body":9,"binderInfo":"default"}}
{"ie":11,"forallE":{"type":3,"name":6,"body":10,"binderInfo":"default"}}
{"ie":12,"forallE":{"type":0,"name":3,"body":11,"binderInfo":"implicit"}}
{"str":{"str":"rec","pre":1},"in":8}
{"str":{"str":"u_1","pre":0},"in":9}
{"param":9,"il":3}
{"str":{"str":"motive","pre":0},"in":10}
{"str":{"str":"t","pre":0},"in":11}
{"sort":3,"ie":13}
{"ie":14,"forallE":{"type":4,"name":11,"body":13,"binderInfo":"default"}}
{"str":{"str":"nil","pre":0},"in":12}
{"ie":15,"const":{"us":[1],"name":4}}
{"ie":16,"app":{"fn":15,"arg":6}}
{"ie":17,"app":{"fn":3,"arg":16}}
{"str":{"str":"cons","pre":0},"in":13}
{"ie":18,"bvar":3}
{"ie":19,"app":{"fn":2,"arg":18}}
{"str":{"str":"tail_ih","pre":0},"in":14}
{"ie":20,"app":{"fn":18,"arg":3}}
{"ie":21,"bvar":4}
{"ie":22,"const":{"us":[1],"name":5}}
{"ie":23,"bvar":5}
{"ie":24,"app":{"fn":22,"arg":23}}
{"ie":25,"app":{"fn":24,"arg":8}}
{"ie":26,"app":{"fn":25,"arg":6}}
{"ie":27,"app":{"fn":21,"arg":26}}
{"ie":28,"forallE":{"type":20,"name":14,"body":27,"binderInfo":"default"}}
{"ie":29,"forallE":{"type":19,"name":7,"body":28,"binderInfo":"default"}}
{"ie":30,"forallE":{"type":8,"name":6,"body":29,"binderInfo":"default"}}
{"ie":31,"forallE":{"type":19,"name":11,"body":20,"binderInfo":"default"}}
{"ie":32,"forallE":{"type":30,"name":13,"body":31,"binderInfo":"default"}}
{"ie":33,"forallE":{"type":17,"name":12,"body":32,"binderInfo":"default"}}
{"ie":34,"forallE":{"type":14,"name":10,"body":33,"binderInfo":"implicit"}}
{"ie":35,"forallE":{"type":0,"name":3,"body":34,"binderInfo":"implicit"}}
{"lam":{"type":30,"name":13,"body":6,"binderInfo":"default"},"ie":36}
{"lam":{"type":17,"name":12,"body":36,"binderInfo":"default"},"ie":37}
{"lam":{"type":14,"name":10,"body":37,"binderInfo":"default"},"ie":38}
{"lam":{"type":0,"name":3,"body":38,"binderInfo":"default"},"ie":39}
{"ie":40,"app":{"fn":2,"arg":21}}
{"ie":41,"app":{"fn":8,"arg":6}}
{"ie":42,"app":{"fn":41,"arg":3}}
{"ie":43,"const":{"us":[3,1],"name":8}}
{"ie":44,"app":{"fn":43,"arg":23}}
{"ie":45,"app":{"fn":44,"arg":21}}
{"ie":46,"app":{"fn":45,"arg":18}}
{"ie":47,"app":{"fn":46,"arg":8}}
{"ie":48,"app":{"fn":47,"arg":3}}
{"ie":49,"app":{"fn":42,"arg":48}}
{"lam":{"type":40,"name":7,"body":49,"binderInfo":"default"},"ie":50}
{"lam":{"type":18,"name":6,"body":50,"binderInfo":"default"},"ie":51}
{"lam":{"type":30,"name":13,"body":51,"binderInfo":"default"},"ie":52}
{"lam":{"type":17,"name":12,"body":52,"binderInfo":"default"},"ie":53}
{"lam":{"type":14,"name":10,"body":53,"binderInfo":"default"},"ie":54}
{"lam":{"type":0,"name":3,"body":54,"binderInfo":"default"},"ie":55}
{"inductive":{"types":[{"type":1,"numParams":1,"numNested":0,"numIndices":0,"name":1,"levelParams":[2],"isUnsafe":false,"isReflexive":false,"isRec":true,"ctors":[4,5],"all":[1]}],"recs":[{"type":35,"rules":[{"rhs":39,"nfields":0,"ctor":4},{"rhs":55,"nfields":2,"ctor":5}],"numParams":1,"numMotives":1,"numMinors":2,"numIndices":0,"name":8,"levelParams":[9,2],"k":false,"isUnsafe":false,"all":[1]}],"ctors":[{"type":5,"numParams":1,"numFields":0,"name":4,"levelParams":[2],"isUnsafe":false,"induct":1,"cidx":0},{"type":12,"numParams":1,"numFields":2,"name":5,"levelParams":[2],"isUnsafe":false,"induct":1,"cidx":1}]}}
-/
#guard_msgs in
#eval run do
  initState (← read).env
  dumpConstant `List

/--
info: {"str":{"str":"Lean","pre":0},"in":1}
{"str":{"str":"opaqueId","pre":1},"in":2}
{"str":{"str":"u","pre":0},"in":3}
{"param":3,"il":1}
{"str":{"str":"α","pre":0},"in":4}
{"sort":1,"ie":0}
{"str":{"str":"x","pre":0},"in":5}
{"ie":1,"bvar":0}
{"ie":2,"bvar":1}
{"ie":3,"forallE":{"type":1,"name":5,"body":2,"binderInfo":"default"}}
{"ie":4,"forallE":{"type":0,"name":4,"body":3,"binderInfo":"implicit"}}
{"lam":{"type":1,"name":5,"body":1,"binderInfo":"default"},"ie":5}
{"lam":{"type":0,"name":4,"body":5,"binderInfo":"implicit"},"ie":6}
{"opaque":{"value":6,"type":4,"name":2,"levelParams":[3],"isUnsafe":false,"all":[2]}}
-/
#guard_msgs in
#eval run do
  initState (← read).env
  dumpConstant ``opaqueId

/-!
Parser tests (we check that that it can be parsed and that the names are correct)
-/

def runParserTest (dump : M Unit) : MetaM Unit := do
  let bufferRef ← IO.mkRef {data := .empty, pos := 0}
  let stream := .ofBuffer bufferRef
  IO.withStdout stream <| do
    run do
      initState (← read).env
      dumpMetadata
      dump
  bufferRef.modify fun buf => { buf with pos := 0 }
  let env ← Export.parseStream stream
  env.constOrder.forM fun n => IO.println n


/--
info: List
List.nil
List.cons
List.rec
-/
#guard_msgs in
#eval runParserTest do
  dumpConstant `List

/--
info: Bool
Bool.false
Bool.true
Bool.rec
sorryAx
-/
#guard_msgs in
#eval runParserTest do
  dumpConstant `sorryAx

/--
info: Eq
Eq.refl
Eq.rec
Quot
Quot.mk
Quot.lift
Quot.ind
-/
#guard_msgs in
#eval runParserTest do
  dumpConstant `Quot.mk

/--
info: Eq
Eq.refl
Eq.rec
Quot
Quot.mk
Quot.lift
Quot.ind
-/
#guard_msgs in
#eval runParserTest do
  dumpConstant `Quot.lift

/-- info: Lean.opaqueId -/
#guard_msgs in
#eval runParserTest do
  dumpConstant ``opaqueId

/-- info: Function.const -/
#guard_msgs in
#eval runParserTest do
  dumpConstant ``Function.const

def functionWithLet  : true = true :=
  let x := true
  Eq.refl x

/--
info: Eq
Eq.refl
Eq.rec
Bool
Bool.false
Bool.true
Bool.rec
functionWithLet
-/
#guard_msgs in
#eval runParserTest do
  dumpConstant ``functionWithLet

def literals : Nat × String := (42, "42")

/--
info: Prod
Prod.mk
Prod.rec
Nat
Nat.zero
Nat.succ
Nat.rec
List
List.nil
List.cons
List.rec
LT
LT.mk
LT.rec
LT.lt
Nat.le
Nat.le.refl
Nat.le.step
Nat.le.rec
Nat.lt
instLTNat
Fin
Fin.mk
Fin.rec
outParam
HPow
HPow.mk
HPow.rec
HPow.hPow
Pow
Pow.mk
Pow.rec
Pow.pow
instHPow
NatPow
NatPow.mk
NatPow.rec
NatPow.pow
instPowNat
PUnit
PUnit.unit
PUnit.rec
PProd
PProd.mk
PProd.rec
Nat.below
Nat.brecOn
Unit
OfNat
OfNat.mk
OfNat.rec
OfNat.ofNat
instOfNatNat
Nat.casesOn
Unit.unit
Nat.pow.match_1
Nat.mul.match_1
Nat.add.match_1
Nat.add
Nat.mul
Nat.pow
instNatPowNat
BitVec
BitVec.ofFin
BitVec.rec
UInt32
UInt32.ofBitVec
UInt32.rec
Or
Or.inl
Or.inr
Or.rec
And
And.intro
And.rec
Nat.isValidChar
Fin.val
BitVec.toFin
BitVec.toNat
UInt32.toBitVec
UInt32.toNat
UInt32.isValidChar
Char
Char.mk
Char.rec
String
String.mk
String.rec
False
False.rec
Not
Decidable
Decidable.isFalse
Decidable.isTrue
Decidable.rec
Decidable.casesOn
dite
instDecidableAnd.match_1
Or.casesOn
instDecidableOr.match_1
instDecidableOr._proof_4
instDecidableOr
LE
LE.mk
LE.rec
LE.le
instLENat
Eq
Eq.refl
Eq.rec
Bool
Bool.false
Bool.true
Bool.rec
Nat.beq.match_1
Nat.ble
DecidableEq
Bool.casesOn
Bool.decEq.match_1
rfl
Bool.noConfusionType
Eq.ndrec
Bool.noConfusion
Bool.decEq
instDecidableEqBool
Eq.casesOn
HEq
HEq.refl
HEq.rec
Nat.le_of_ble_eq_true.match_1
Nat.zero_le.match_1
Nat.zero_le
Nat.le.below
Nat.le.below.refl
Nat.le.below.step
Nat.le.below.rec
Nat.le.brecOn
Nat.le.below.casesOn
Eq.symm
letFun
cast
eq_of_heq
Nat.succ_le_succ.match_1._@.Init.Prelude._hyg.3560
HAdd
HAdd.mk
HAdd.rec
HAdd.hAdd
Add
Add.mk
Add.rec
Add.add
instHAdd
instAddNat
Nat.succ_le_succ
Nat.le_of_ble_eq_true
absurd
Nat.ble_eq_true_of_le.match_1._@.Init.Prelude._hyg.4182
Nat.ble_self_eq_true.match_1
Nat.ble_self_eq_true
Nat.ble_succ_eq_true.match_1
Nat.ble_succ_eq_true
Nat.ble_eq_true_of_le
Nat.not_le_of_not_ble_eq_true
Nat.decLe
Nat.decLt
And.right
instDecidableAnd._proof_2
And.left
instDecidableAnd._proof_3
instDecidableAnd
BitVec.ofNatLT
UInt32.size
And.casesOn
_private.Init.Prelude.0.isValidChar_UInt32.match_1
Nat.le_trans.match_1._@.Init.Prelude._hyg.3649
Nat.le_trans
Nat.le_step
Nat.lt_trans
Decidable.decide
of_decide_eq_true.match_1
ne_true_of_eq_false.match_1
ne_true_of_eq_false
decide_eq_false.match_1
decide_eq_false
of_decide_eq_true
_private.Init.Prelude.0.isValidChar_UInt32
Char.ofNatAux
Char.ofNat._proof_23
Char.ofNat._proof_24
Char.ofNat
literals
-/
#guard_msgs in
#eval runParserTest do
  dumpConstant ``literals
