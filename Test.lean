import Export
open Lean

def run (act : M α) : MetaM Unit := do let _ ← M.run (← getEnv) act

/--
info: 1 #NS 0 foo
2 #NS 1 bla
3 #NI 2 1
4 #NS 3 boo
-/
#guard_msgs in
#eval run <| dumpName (`foo.bla |>.num 1 |>.str "boo")

/--
info: 1 #US 0
2 #US 1
1 #NS 0 l1
3 #UP 1
4 #UM 2 3
2 #NS 0 l2
5 #UP 2
6 #UIM 4 5
-/
#guard_msgs in
#eval run <| dumpLevel (.imax (.max (.succ (.succ .zero)) (.param `l1)) (.param `l2))

/--
info: 1 #NS 0 A
1 #US 0
0 #ES 1
2 #NS 0 a
1 #EV 0
2 #EL #BD 2 1 1
3 #EL #BI 1 0 2
-/
#guard_msgs in
#eval run <| dumpExpr (.lam `A (.sort (.succ .zero)) (.lam `a (.bvar 0) (.bvar 0) .default) .implicit)

/--
info: 1 #NS 0 x
2 #NS 0 Nat
0 #EC 2 ⏎
3 #NS 2 zero
1 #EC 3 ⏎
2 #EV 0
3 #EZ 1 0 1 2
-/
#guard_msgs in
#eval run <| dumpExpr (.letE `x (.const `Nat []) (.const `Nat.zero []) (.bvar 0) false)

/--
info: 1 #NS 0 Prod
0 #EV 0
1 #EJ 1 1 0
-/
#guard_msgs in
#eval run <| dumpExpr (.proj `Prod 1 (.bvar 0))

/-- info: 0 #ELN 1000000000000000 -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.natVal 1000000000000000))

/-- info: 0 #ELS 68 69 -/
#guard_msgs in
#eval run <| dumpExpr (.lit (.strVal "hi"))

/--
info: 1 #NS 0 id
2 #NS 0 α
3 #NS 0 u
1 #UP 3
0 #ES 1
4 #NS 0 a
1 #EV 0
2 #EV 1
3 #EP #BD 4 1 2
4 #EP #BI 2 0 3
5 #EL #BD 4 1 1
6 #EL #BI 2 0 5
#DEF 1 4 6 3
-/
#guard_msgs in
#eval run <| dumpConstant `id

/--
info: 1 #NS 0 List
2 #NS 1 nil
3 #NS 0 α
4 #NS 0 u
1 #UP 4
2 #US 1
0 #ES 2
1 #EC 1 1
2 #EV 0
3 #EA 1 2
4 #EP #BI 3 0 3
5 #NS 1 cons
6 #NS 0 head
7 #NS 0 tail
5 #EV 1
6 #EA 1 5
7 #EV 2
8 #EA 1 7
9 #EP #BD 7 6 8
10 #EP #BD 6 2 9
11 #EP #BI 3 0 10
12 #EP #BD 3 0 0
#IND 1 1 12 2 2 4 5 11 4
-/
#guard_msgs in
#eval run <| dumpConstant `List
