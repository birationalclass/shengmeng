module
import all Linear.InjectiveCocycleExtPresentation
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.injectiveCocycleGroup
#print axioms LinearStudy.injectiveCocycleGroup
#check @LinearStudy.injectiveCocycleExtMap
#print axioms LinearStudy.injectiveCocycleExtMap
#check @LinearStudy.injectiveCocycleExtMap_surjective
#print axioms LinearStudy.injectiveCocycleExtMap_surjective
#check @LinearStudy.injectiveCocycleExtMap_succ_eq_zero_iff
#print axioms LinearStudy.injectiveCocycleExtMap_succ_eq_zero_iff
#print LinearStudy.injectiveCocycleGroup
#print LinearStudy.injectiveCocycleExtMap
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.injectiveCocycleGroup,false),(`LinearStudy.injectiveCocycleExtMap,false),(`LinearStudy.injectiveCocycleExtMap_surjective,true),(`LinearStudy.injectiveCocycleExtMap_succ_eq_zero_iff,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
