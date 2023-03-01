import Export
open Lean

def run (act : M α) : MetaM Unit := do let _ ← M.run (← getEnv) act

#eval run <| dumpName (`foo.bla |>.num 1 |>.str "boo")

#eval run <| dumpLevel (.imax (.max (.succ (.succ .zero)) (.param `l1)) (.param `l2))

#eval run <| dumpExpr (.lam `A (.sort (.succ .zero)) (.lam `a (.bvar 0) (.bvar 0) .default) .implicit)

#eval run <| dumpExpr (.letE `x (.const `Nat []) (.const `Nat.zero []) (.bvar 0) false)

#eval run <| dumpExpr (.proj `Prod 1 (.bvar 0))

#eval run <| dumpExpr (.lit (.natVal 1000000000000000))
#eval run <| dumpExpr (.lit (.strVal "hi"))

#eval run <| dumpConstant `id
#eval run <| dumpConstant `List
