module
import all Linear.SchemeModuleInjectiveFlasque
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModule_injective_globalRestriction_surjective
#print axioms LinearStudy.schemeModule_injective_globalRestriction_surjective
#check @LinearStudy.schemeModule_injective_isFlasque
#print axioms LinearStudy.schemeModule_injective_isFlasque
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModule_injective_globalRestriction_surjective,true),(`LinearStudy.schemeModule_injective_isFlasque,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
