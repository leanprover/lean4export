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
info: {"in":1,"str":{"pre":0,"str":"foo"}}
{"in":2,"str":{"pre":1,"str":"bla"}}
{"in":3,"num":{"i":1,"pre":2}}
{"in":4,"str":{"pre":3,"str":"boo"}}
-/
#guard_msgs in
#eval run <| dumpName (`foo.bla |>.num 1 |>.str "boo")

/--
info: {"in":1,"str":{"pre":0,"str":"\npq\n  \nrs\u0009\r\nuv\n\n"}}
-/
#guard_msgs in
#eval run <| dumpName (Name.str Name.anonymous "\npq\n  \nrs\t\r\nuv\n\n")

/--
info: {"il":1,"succ":0}
{"il":2,"succ":1}
{"in":1,"str":{"pre":0,"str":"l1"}}
{"il":3,"param":1}
{"il":4,"max":[2,3]}
{"in":2,"str":{"pre":0,"str":"l2"}}
{"il":5,"param":2}
{"il":6,"imax":[4,5]}
-/
#guard_msgs in
#eval run <| dumpLevel (.imax (.max (.succ (.succ .zero)) (.param `l1)) (.param `l2))

/--
info: {"in":1,"str":{"pre":0,"str":"A"}}
{"il":1,"succ":0}
{"ie":0,"sort":1}
{"in":2,"str":{"pre":0,"str":"a"}}
{"bvar":0,"ie":1}
{"ie":2,"lam":{"binderInfo":"default","body":1,"name":2,"type":1}}
{"ie":3,"lam":{"binderInfo":"implicit","body":2,"name":1,"type":0}}
-/
#guard_msgs in
#eval run <| dumpExpr (.lam `A (.sort (.succ .zero)) (.lam `a (.bvar 0) (.bvar 0) .default) .implicit)

/--
info: {"in":1,"str":{"pre":0,"str":"x"}}
{"in":2,"str":{"pre":0,"str":"Nat"}}
{"const":{"name":2,"us":[]},"ie":0}
{"in":3,"str":{"pre":2,"str":"zero"}}
{"const":{"name":3,"us":[]},"ie":1}
{"bvar":0,"ie":2}
{"ie":3,"letE":{"body":2,"name":1,"nondep":false,"type":0,"value":1}}
-/
#guard_msgs in
#eval run <| dumpExpr (.letE `x (.const `Nat []) (.const `Nat.zero []) (.bvar 0) false)

/--
info: {"in":1,"str":{"pre":0,"str":"Prod"}}
{"bvar":0,"ie":0}
{"ie":1,"proj":{"idx":1,"struct":0,"typeName":1}}
-/
#guard_msgs in
#eval run <| dumpExpr (.proj `Prod 1 (.bvar 0))

/-- info: {"ie":0,"natVal":"100000000000000023456789"}
-/
#guard_msgs in
#eval runEmpty <| dumpExpr (.lit (.natVal 100000000000000023456789))

/--
info: {"in":1,"str":{"pre":0,"str":"Nat"}}
{"il":1,"succ":0}
{"ie":0,"sort":1}
{"in":2,"str":{"pre":1,"str":"zero"}}
{"in":3,"str":{"pre":1,"str":"succ"}}
{"const":{"name":1,"us":[]},"ie":1}
{"in":4,"str":{"pre":0,"str":"n"}}
{"forallE":{"binderInfo":"default","body":1,"name":4,"type":1},"ie":2}
{"in":5,"str":{"pre":1,"str":"rec"}}
{"in":6,"str":{"pre":0,"str":"u"}}
{"il":2,"param":6}
{"in":7,"str":{"pre":0,"str":"motive"}}
{"in":8,"str":{"pre":0,"str":"t"}}
{"ie":3,"sort":2}
{"forallE":{"binderInfo":"default","body":3,"name":8,"type":1},"ie":4}
{"in":9,"str":{"pre":0,"str":"zero"}}
{"bvar":0,"ie":5}
{"const":{"name":2,"us":[]},"ie":6}
{"app":{"arg":6,"fn":5},"ie":7}
{"in":10,"str":{"pre":0,"str":"succ"}}
{"in":11,"str":{"pre":0,"str":"n_ih"}}
{"bvar":2,"ie":8}
{"app":{"arg":5,"fn":8},"ie":9}
{"bvar":3,"ie":10}
{"const":{"name":3,"us":[]},"ie":11}
{"bvar":1,"ie":12}
{"app":{"arg":12,"fn":11},"ie":13}
{"app":{"arg":13,"fn":10},"ie":14}
{"forallE":{"binderInfo":"default","body":14,"name":11,"type":9},"ie":15}
{"forallE":{"binderInfo":"default","body":15,"name":4,"type":1},"ie":16}
{"app":{"arg":5,"fn":10},"ie":17}
{"forallE":{"binderInfo":"default","body":17,"name":8,"type":1},"ie":18}
{"forallE":{"binderInfo":"default","body":18,"name":10,"type":16},"ie":19}
{"forallE":{"binderInfo":"default","body":19,"name":9,"type":7},"ie":20}
{"forallE":{"binderInfo":"implicit","body":20,"name":7,"type":4},"ie":21}
{"ie":22,"lam":{"binderInfo":"default","body":12,"name":10,"type":16}}
{"ie":23,"lam":{"binderInfo":"default","body":22,"name":9,"type":7}}
{"ie":24,"lam":{"binderInfo":"default","body":23,"name":7,"type":4}}
{"app":{"arg":5,"fn":12},"ie":25}
{"const":{"name":5,"us":[2]},"ie":26}
{"app":{"arg":10,"fn":26},"ie":27}
{"app":{"arg":8,"fn":27},"ie":28}
{"app":{"arg":12,"fn":28},"ie":29}
{"app":{"arg":5,"fn":29},"ie":30}
{"app":{"arg":30,"fn":25},"ie":31}
{"ie":32,"lam":{"binderInfo":"default","body":31,"name":4,"type":1}}
{"ie":33,"lam":{"binderInfo":"default","body":32,"name":10,"type":16}}
{"ie":34,"lam":{"binderInfo":"default","body":33,"name":9,"type":7}}
{"ie":35,"lam":{"binderInfo":"default","body":34,"name":7,"type":4}}
{"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":2,"numFields":0,"numParams":0,"type":1},{"cidx":1,"induct":1,"isUnsafe":false,"levelParams":[],"name":3,"numFields":1,"numParams":0,"type":2}],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[6],"name":5,"numIndices":0,"numMinors":2,"numMotives":1,"numParams":0,"rules":[{"ctor":2,"nfields":0,"rhs":24},{"ctor":3,"nfields":1,"rhs":35}],"type":21}],"types":[{"all":[1],"ctors":[2,3],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":0,"type":0}]}}
{"ie":36,"natVal":"100000000000000023456789"}
-/
#guard_msgs in
#eval run <| dumpExpr (.lit (.natVal 100000000000000023456789))

/-- info: {"ie":0,"strVal":"hi"} -/
#guard_msgs in
#eval runEmpty <| dumpExpr (.lit (.strVal "hi"))

/-- info: {"ie":0,"strVal":"\r\rh\ni\u0009\u0009"} -/
#guard_msgs in
#eval runEmpty <| dumpExpr (.lit (.strVal "\r\rh
i\t\t"))

/-- info: {"ie":0,"strVal":"اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр"} -/
#guard_msgs in
#eval runEmpty <| dumpExpr
  (.lit (.strVal "اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр"))

/--
info: {"in":1,"str":{"pre":0,"str":"id"}}
{"in":2,"str":{"pre":0,"str":"u"}}
{"il":1,"param":2}
{"in":3,"str":{"pre":0,"str":"α"}}
{"ie":0,"sort":1}
{"in":4,"str":{"pre":0,"str":"a"}}
{"bvar":0,"ie":1}
{"bvar":1,"ie":2}
{"forallE":{"binderInfo":"default","body":2,"name":4,"type":1},"ie":3}
{"forallE":{"binderInfo":"implicit","body":3,"name":3,"type":0},"ie":4}
{"ie":5,"lam":{"binderInfo":"default","body":1,"name":4,"type":1}}
{"ie":6,"lam":{"binderInfo":"implicit","body":5,"name":3,"type":0}}
{"def":{"all":[1],"hints":{"regular":1},"levelParams":[2],"name":1,"safety":"safe","type":4,"value":6}}
-/
#guard_msgs in
#eval run <| do
  initState (← read).env
  dumpConstant `id

/--
info: {"in":1,"str":{"pre":0,"str":"List"}}
{"in":2,"str":{"pre":0,"str":"u"}}
{"il":1,"param":2}
{"in":3,"str":{"pre":0,"str":"α"}}
{"il":2,"succ":1}
{"ie":0,"sort":2}
{"forallE":{"binderInfo":"default","body":0,"name":3,"type":0},"ie":1}
{"in":4,"str":{"pre":1,"str":"nil"}}
{"in":5,"str":{"pre":1,"str":"cons"}}
{"const":{"name":1,"us":[1]},"ie":2}
{"bvar":0,"ie":3}
{"app":{"arg":3,"fn":2},"ie":4}
{"forallE":{"binderInfo":"implicit","body":4,"name":3,"type":0},"ie":5}
{"in":6,"str":{"pre":0,"str":"head"}}
{"in":7,"str":{"pre":0,"str":"tail"}}
{"bvar":1,"ie":6}
{"app":{"arg":6,"fn":2},"ie":7}
{"bvar":2,"ie":8}
{"app":{"arg":8,"fn":2},"ie":9}
{"forallE":{"binderInfo":"default","body":9,"name":7,"type":7},"ie":10}
{"forallE":{"binderInfo":"default","body":10,"name":6,"type":3},"ie":11}
{"forallE":{"binderInfo":"implicit","body":11,"name":3,"type":0},"ie":12}
{"in":8,"str":{"pre":1,"str":"rec"}}
{"in":9,"str":{"pre":0,"str":"u_1"}}
{"il":3,"param":9}
{"in":10,"str":{"pre":0,"str":"motive"}}
{"in":11,"str":{"pre":0,"str":"t"}}
{"ie":13,"sort":3}
{"forallE":{"binderInfo":"default","body":13,"name":11,"type":4},"ie":14}
{"in":12,"str":{"pre":0,"str":"nil"}}
{"const":{"name":4,"us":[1]},"ie":15}
{"app":{"arg":6,"fn":15},"ie":16}
{"app":{"arg":16,"fn":3},"ie":17}
{"in":13,"str":{"pre":0,"str":"cons"}}
{"bvar":3,"ie":18}
{"app":{"arg":18,"fn":2},"ie":19}
{"in":14,"str":{"pre":0,"str":"tail_ih"}}
{"app":{"arg":3,"fn":18},"ie":20}
{"bvar":4,"ie":21}
{"const":{"name":5,"us":[1]},"ie":22}
{"bvar":5,"ie":23}
{"app":{"arg":23,"fn":22},"ie":24}
{"app":{"arg":8,"fn":24},"ie":25}
{"app":{"arg":6,"fn":25},"ie":26}
{"app":{"arg":26,"fn":21},"ie":27}
{"forallE":{"binderInfo":"default","body":27,"name":14,"type":20},"ie":28}
{"forallE":{"binderInfo":"default","body":28,"name":7,"type":19},"ie":29}
{"forallE":{"binderInfo":"default","body":29,"name":6,"type":8},"ie":30}
{"forallE":{"binderInfo":"default","body":20,"name":11,"type":19},"ie":31}
{"forallE":{"binderInfo":"default","body":31,"name":13,"type":30},"ie":32}
{"forallE":{"binderInfo":"default","body":32,"name":12,"type":17},"ie":33}
{"forallE":{"binderInfo":"implicit","body":33,"name":10,"type":14},"ie":34}
{"forallE":{"binderInfo":"implicit","body":34,"name":3,"type":0},"ie":35}
{"ie":36,"lam":{"binderInfo":"default","body":6,"name":13,"type":30}}
{"ie":37,"lam":{"binderInfo":"default","body":36,"name":12,"type":17}}
{"ie":38,"lam":{"binderInfo":"default","body":37,"name":10,"type":14}}
{"ie":39,"lam":{"binderInfo":"default","body":38,"name":3,"type":0}}
{"app":{"arg":21,"fn":2},"ie":40}
{"app":{"arg":6,"fn":8},"ie":41}
{"app":{"arg":3,"fn":41},"ie":42}
{"const":{"name":8,"us":[3,1]},"ie":43}
{"app":{"arg":23,"fn":43},"ie":44}
{"app":{"arg":21,"fn":44},"ie":45}
{"app":{"arg":18,"fn":45},"ie":46}
{"app":{"arg":8,"fn":46},"ie":47}
{"app":{"arg":3,"fn":47},"ie":48}
{"app":{"arg":48,"fn":42},"ie":49}
{"ie":50,"lam":{"binderInfo":"default","body":49,"name":7,"type":40}}
{"ie":51,"lam":{"binderInfo":"default","body":50,"name":6,"type":18}}
{"ie":52,"lam":{"binderInfo":"default","body":51,"name":13,"type":30}}
{"ie":53,"lam":{"binderInfo":"default","body":52,"name":12,"type":17}}
{"ie":54,"lam":{"binderInfo":"default","body":53,"name":10,"type":14}}
{"ie":55,"lam":{"binderInfo":"default","body":54,"name":3,"type":0}}
{"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[2],"name":4,"numFields":0,"numParams":1,"type":5},{"cidx":1,"induct":1,"isUnsafe":false,"levelParams":[2],"name":5,"numFields":2,"numParams":1,"type":12}],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[9,2],"name":8,"numIndices":0,"numMinors":2,"numMotives":1,"numParams":1,"rules":[{"ctor":4,"nfields":0,"rhs":39},{"ctor":5,"nfields":2,"rhs":55}],"type":35}],"types":[{"all":[1],"ctors":[4,5],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[2],"name":1,"numIndices":0,"numNested":0,"numParams":1,"type":1}]}}
-/
#guard_msgs in
#eval run do
  initState (← read).env
  dumpConstant `List

/--
info: {"in":1,"str":{"pre":0,"str":"Lean"}}
{"in":2,"str":{"pre":1,"str":"opaqueId"}}
{"in":3,"str":{"pre":0,"str":"u"}}
{"il":1,"param":3}
{"in":4,"str":{"pre":0,"str":"α"}}
{"ie":0,"sort":1}
{"in":5,"str":{"pre":0,"str":"x"}}
{"bvar":0,"ie":1}
{"bvar":1,"ie":2}
{"forallE":{"binderInfo":"default","body":2,"name":5,"type":1},"ie":3}
{"forallE":{"binderInfo":"implicit","body":3,"name":4,"type":0},"ie":4}
{"ie":5,"lam":{"binderInfo":"default","body":1,"name":5,"type":1}}
{"ie":6,"lam":{"binderInfo":"implicit","body":5,"name":4,"type":0}}
{"opaque":{"all":[2],"isUnsafe":false,"levelParams":[3],"name":2,"type":4,"value":6}}
-/
#guard_msgs in
#eval run do
  initState (← read).env
  dumpConstant ``opaqueId

/-!
Parser tests (we check that that it can be parsed and that the names are correct)
-/

meta def runParserTest (dump : M Unit) : MetaM Unit := do
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
Quot.lift
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
Array
Array.mk
Array.rec
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
Nat.brecOn.go
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
UInt8
UInt8.ofBitVec
UInt8.rec
ByteArray
ByteArray.mk
ByteArray.rec
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
Eq
Eq.refl
Eq.rec
List.below
List.brecOn.go
List.brecOn
List.casesOn
List.toByteArray.match_1
ByteArray.casesOn
ByteArray.push.match_1
List.concat.match_1
List.concat
Array.toList
Array.push
ByteArray.push
List.toByteArray.loop
Array.emptyWithCapacity
Array.empty
ByteArray.emptyWithCapacity
ByteArray.empty
List.toByteArray
List.flatten.match_1
List.append.match_1
List.append
List.flatten
instDecidableEqList.match_1
List.map
List.flatMap
Char.val
False
False.rec
Not
Decidable
Decidable.isFalse
Decidable.isTrue
Decidable.rec
Decidable.casesOn
ite
LE
LE.mk
LE.rec
LE.le
instLENat
dite
Bool
Bool.false
Bool.true
Bool.rec
Nat.ble.match_1
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
False.elim
Eq.casesOn
HEq
HEq.refl
HEq.rec
True
True.intro
True.rec
Nat.beq.match_1
Nat.beq
_private.Init.Prelude.0.noConfusion_of_Nat.aux.match_1_1
_private.Init.Prelude.0.noConfusion_of_Nat.aux
congrArg
noConfusion_of_Nat
Bool.ctorIdx
_private.Init.Prelude.0.Nat.le_of_ble_eq_true.match_1_1
_private.Init.Prelude.0.Nat.zero_le.match_1_1
Nat.zero_le
Nat.le.below
Nat.le.below.refl
Nat.le.below.step
Nat.le.below.rec
Nat.le.brecOn
Nat.le.below.casesOn
Eq.symm
cast
eq_of_heq
_private.Init.Prelude.0.Nat.succ_le_succ.match_1_4
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
_private.Init.Prelude.0.Nat.ble_eq_true_of_le.match_1_4
_private.Init.Prelude.0.Nat.ble_self_eq_true.match_1_1
Nat.ble_self_eq_true
_private.Init.Prelude.0.Nat.ble_succ_eq_true.match_1_1
Nat.ble_succ_eq_true
Nat.ble_eq_true_of_le
Nat.not_le_of_not_ble_eq_true
Nat.decLe
HMod
HMod.mk
HMod.rec
HMod.hMod
Mod
Mod.mk
Mod.rec
Mod.mod
instHMod
namedPattern
Nat.mod.match_1
Nat.decLt
Nat.le.casesOn
Nat.ctorIdx
Nat.div.go.match_1
HSub
HSub.mk
HSub.rec
HSub.hSub
Sub
Sub.mk
Sub.rec
Sub.sub
instHSub
Nat.pred
Nat.sub
instSubNat
_private.Init.Prelude.0.Nat.le_trans.match_1_6
Nat.le_trans
Nat.lt_of_lt_of_le
And.casesOn
_private.Init.Prelude.0.Nat.div_rec_lemma.match_1_1
_private.Init.Prelude.0.Nat.sub_lt.match_1_1
_private.Init.Prelude.0.Nat.not_succ_le_self.match_1_1
Nat.noConfusionType
Nat.noConfusion
Nat.not_succ_le_zero
_private.Init.Prelude.0.Nat.pred_le_pred.match_1_1
Nat.le_succ
Nat.pred_le_pred
Nat.le_of_succ_le_succ
Nat.not_succ_le_self
Nat.lt_irrefl
Nat.lt_succ_of_le
Nat.le_refl
_private.Init.Prelude.0.Nat.pred_le.match_1_1
Nat.pred_le
Nat.sub_le
Nat.succ_sub_succ_eq_sub
Nat.sub_lt
Nat.div_rec_lemma
Nat.le_of_lt_succ
Nat.div_rec_fuel_lemma
Nat.modCore.go
Nat.lt_add_one
Nat.lt_succ_self
Nat.modCore
Nat.mod
Nat.instMod
_private.Init.Prelude.0.Nat.mod_lt.match_1_3
Nat.zero_lt_succ
_private.Init.Prelude.0.Nat.mod_lt.match_1_1
_private.Init.Prelude.0.Nat.modCore_lt.match_1_1
Nat.not_lt_zero
_private.Init.Prelude.0.Nat.modCoreGo_lt.match_1_1
Or.casesOn
_private.Init.Prelude.0.Or.elim.match_1_1
Or.elim
id
Or.resolve_right
GE.ge
_private.Init.Prelude.0.Nat.lt_or_ge.match_1_5
_private.Init.Prelude.0.Nat.lt_or_ge.match_1_3
Nat.le_succ_of_le
_private.Init.Prelude.0.Nat.lt_or_ge.match_1_1
Nat.eq_or_lt_of_le.match_3
Nat.eq_or_lt_of_le.match_1
Nat.eq_or_lt_of_le
Nat.lt_or_ge
Nat.lt_of_not_le
Nat.modCoreGo_lt
Nat.modCore_lt
Nat.mod_lt
Fin.Internal.ofNat
_private.Init.Prelude.0.Nat.pow_pos.match_1_1
HMul
HMul.mk
HMul.rec
HMul.hMul
Mul
Mul.mk
Mul.rec
Mul.mul
instHMul
instMulNat
_private.Init.Prelude.0.Nat.mul_pos.match_1_1
_private.Init.Prelude.0.Nat.add_pos_right.match_1_1
Nat.add_pos_right
Nat.mul_pos
Nat.pow_pos
BitVec.ofNat._proof_1
BitVec.ofNat
UInt8.ofNat
HDiv
HDiv.mk
HDiv.rec
HDiv.hDiv
Div
Div.mk
Div.rec
Div.div
instHDiv
Nat.div.go
Nat.div
Nat.instDiv
String.utf8EncodeChar
List.utf8Encode
ByteArray.IsValidUTF8
ByteArray.IsValidUTF8.intro
ByteArray.IsValidUTF8.rec
String
String.ofByteArray
String.rec
instDecidableAnd.match_1
instDecidableOr.match_1
instDecidableOr._proof_1
instDecidableOr
And.right
instDecidableAnd._proof_1
And.left
instDecidableAnd._proof_2
instDecidableAnd
BitVec.ofNatLT
UInt32.size
_private.Init.Prelude.0.isValidChar_UInt32.match_1_1
Nat.lt_trans
Decidable.decide
_private.Init.Prelude.0.of_decide_eq_true.match_1_1
_private.Init.Prelude.0.ne_true_of_eq_false.match_1_1
ne_true_of_eq_false
_private.Init.Prelude.0.decide_eq_false.match_1_1
decide_eq_false
of_decide_eq_true
_private.Init.Prelude.0.isValidChar_UInt32
Char.ofNatAux._private_1
Char.ofNatAux
Char.ofNat._proof_1
Char.ofNat._proof_2
Char.ofNat
String.ofList._proof_1
String.ofList
literals
-/
#guard_msgs in
#eval runParserTest do
  dumpConstant ``literals
