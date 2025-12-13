import Export
open Lean

def run (act : M α) : MetaM Unit := do let _ ← M.run (← getEnv) act

/--
info: {"i":1,"str":{"pre":0,"str":"foo"}}
{"i":2,"str":{"pre":1,"str":"bla"}}
{"i":3,"num":{"i":1,"pre":2}}
{"i":4,"str":{"pre":3,"str":"boo"}}
-/
#guard_msgs in
#eval run <| dumpName (`foo.bla |>.num 1 |>.str "boo")

/--
info: {"i":1,"str":{"pre":0,"str":"\npq\n  \nrs\u0009\r\nuv\n\n"}}
-/
#guard_msgs in
#eval run <| dumpName (Name.str Name.anonymous "\npq\n  \nrs\t\r\nuv\n\n")

/--
info: {"i":1,"succ":0}
{"i":2,"succ":1}
{"i":1,"str":{"pre":0,"str":"l1"}}
{"i":3,"param":1}
{"i":4,"max":[2,3]}
{"i":2,"str":{"pre":0,"str":"l2"}}
{"i":5,"param":2}
{"i":6,"imax":[4,5]}
-/
#guard_msgs in
#eval run <| dumpLevel (.imax (.max (.succ (.succ .zero)) (.param `l1)) (.param `l2))

/--
info: {"i":1,"str":{"pre":0,"str":"A"}}
{"i":1,"succ":0}
{"i":0,"sort":{"u":1}}
{"i":2,"str":{"pre":0,"str":"a"}}
{"bvar":{"deBruijnIndex":0},"i":1}
{"i":2,"lam":{"binderInfo":"default","binderName":2,"binderType":1,"body":1}}
{"i":3,"lam":{"binderInfo":"implicit","binderName":1,"binderType":0,"body":2}}
-/
#guard_msgs in
#eval run <| dumpExpr (.lam `A (.sort (.succ .zero)) (.lam `a (.bvar 0) (.bvar 0) .default) .implicit)

/--
info: {"i":1,"str":{"pre":0,"str":"x"}}
{"i":2,"str":{"pre":0,"str":"Nat"}}
{"const":{"declName":2,"us":[]},"i":0}
{"i":3,"str":{"pre":2,"str":"zero"}}
{"const":{"declName":3,"us":[]},"i":1}
{"bvar":{"deBruijnIndex":0},"i":2}
{"i":3,"letE":{"body":2,"declName":1,"nondep":false,"type":0,"value":1}}
-/
#guard_msgs in
#eval run <| dumpExpr (.letE `x (.const `Nat []) (.const `Nat.zero []) (.bvar 0) false)

/--
info: {"i":1,"str":{"pre":0,"str":"Prod"}}
{"bvar":{"deBruijnIndex":0},"i":0}
{"i":1,"proj":{"idx":1,"struct":0,"typeName":1}}
-/
#guard_msgs in
#eval run <| dumpExpr (.proj `Prod 1 (.bvar 0))

/-- info: {"i":0,"natVal":"1000000000000000"} -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.natVal 1000000000000000))


/-- info: {"i":0,"natVal":"123456789"} -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.natVal 123456789))

/-- info: {"i":0,"strVal":"hi"} -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.strVal "hi"))

/-- info: {"i":0,"strVal":"\r\rh\ni\u0009\u0009"} -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.strVal "\r\rh
i\t\t"))

/-- info: {"i":0,"strVal":"اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр"} -/
#guard_msgs in
#eval run <| dumpExpr
  (.lit (.strVal "اَلْعَرَبِيَّةُ اُرْدُو 普通话 日本語 廣東話 русский язык עִבְרִית‎ 한국어 aаoοpр"))

/--
info: {"i":1,"str":{"pre":0,"str":"id"}}
{"i":2,"str":{"pre":0,"str":"u"}}
{"i":1,"param":2}
{"i":3,"str":{"pre":0,"str":"α"}}
{"i":0,"sort":{"u":1}}
{"i":4,"str":{"pre":0,"str":"a"}}
{"bvar":{"deBruijnIndex":0},"i":1}
{"bvar":{"deBruijnIndex":1},"i":2}
{"forallE":{"binderInfo":"default","binderName":4,"binderType":1,"body":2},"i":3}
{"forallE":{"binderInfo":"implicit","binderName":3,"binderType":0,"body":3},"i":4}
{"i":5,"lam":{"binderInfo":"default","binderName":4,"binderType":1,"body":1}}
{"i":6,"lam":{"binderInfo":"implicit","binderName":3,"binderType":0,"body":5}}
{"defnInfo":{"all":[1],"hints":{"regular":1},"levelParams":[2],"name":1,"safety":"safe","type":4,"value":6}}
-/
#guard_msgs in
#eval run <| dumpConstant `id

/--
info: {"i":1,"str":{"pre":0,"str":"List"}}
{"i":2,"str":{"pre":0,"str":"u"}}
{"i":1,"param":2}
{"i":3,"str":{"pre":0,"str":"α"}}
{"i":2,"succ":1}
{"i":0,"sort":{"u":2}}
{"forallE":{"binderInfo":"default","binderName":3,"binderType":0,"body":0},"i":1}
{"i":4,"str":{"pre":1,"str":"nil"}}
{"i":5,"str":{"pre":1,"str":"cons"}}
{"inductInfo":{"all":[1],"ctors":[4,5],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[2],"name":1,"numIndices":0,"numNested":0,"numParams":1,"type":1}}
{"const":{"declName":1,"us":[1]},"i":2}
{"bvar":{"deBruijnIndex":0},"i":3}
{"app":{"arg":3,"fn":2},"i":4}
{"forallE":{"binderInfo":"implicit","binderName":3,"binderType":0,"body":4},"i":5}
{"ctorInfo":{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[2],"name":4,"numFields":0,"numParams":1,"type":5}}
{"i":6,"str":{"pre":0,"str":"head"}}
{"i":7,"str":{"pre":0,"str":"tail"}}
{"bvar":{"deBruijnIndex":1},"i":6}
{"app":{"arg":6,"fn":2},"i":7}
{"bvar":{"deBruijnIndex":2},"i":8}
{"app":{"arg":8,"fn":2},"i":9}
{"forallE":{"binderInfo":"default","binderName":7,"binderType":7,"body":9},"i":10}
{"forallE":{"binderInfo":"default","binderName":6,"binderType":3,"body":10},"i":11}
{"forallE":{"binderInfo":"implicit","binderName":3,"binderType":0,"body":11},"i":12}
{"ctorInfo":{"cidx":1,"induct":1,"isUnsafe":false,"levelParams":[2],"name":5,"numFields":2,"numParams":1,"type":12}}
-/
#guard_msgs in
#eval run <| dumpConstant `List
