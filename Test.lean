import Export
open Lean

def run (act : M α) : MetaM Unit := do let _ ← M.run (← getEnv) act

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

/-- info: {"ie":0,"natVal":"1000000000000000"} -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.natVal 1000000000000000))


/-- info: {"ie":0,"natVal":"123456789"} -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.natVal 123456789))

/-- info: {"ie":0,"strVal":"hi"} -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.strVal "hi"))

/-- info: {"ie":0,"strVal":"\r\rh\ni\u0009\u0009"} -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.strVal "\r\rh
i\t\t"))

/-- info: {"ie":0,"strVal":"اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр"} -/
#guard_msgs in
#eval run <| dumpExpr
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
{"defnInfo":{"all":[1],"hints":{"regular":1},"levelParams":[2],"name":1,"safety":"safe","type":4,"value":6}}
-/
#guard_msgs in
#eval run <| do
  let _ ← initState (← read).env
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
{"inductive":{"constructorVals":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[2],"name":4,"numFields":0,"numParams":1,"type":5},{"cidx":1,"induct":1,"isUnsafe":false,"levelParams":[2],"name":5,"numFields":2,"numParams":1,"type":12}],"inductiveVals":[{"all":[1],"ctors":[4,5],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[2],"name":1,"numIndices":0,"numNested":0,"numParams":1,"type":1}],"recursorVals":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[9,2],"name":8,"numIndices":0,"numMinors":2,"numMotives":1,"numParams":1,"rules":[{"ctor":4,"nfields":0,"rhs":39},{"ctor":5,"nfields":2,"rhs":55}],"type":35}]}}
-/
#guard_msgs in
#eval run <| do
  let _ ← initState (← read).env
  dumpConstant `List
