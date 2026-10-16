module
import all Linear.CochainConeLiftDerivedBridge
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainDerivedMap_eq_of_classEq
#print axioms LinearStudy.cochainDerivedMap_eq_of_classEq
#check @LinearStudy.cochainConeLiftDerivedBridge
#print axioms LinearStudy.cochainConeLiftDerivedBridge
#check @LinearStudy.cochainConeTriangle_mor3_neg_fst
#print axioms LinearStudy.cochainConeTriangle_mor3_neg_fst
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainDerivedMap_eq_of_classEq,true),(`LinearStudy.cochainConeLiftDerivedBridge,true),(`LinearStudy.cochainConeTriangle_mor3_neg_fst,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
