-- Reaudit after reusing original existing cycleMap_i;no duplicate new theorem.
module
import all Linear.SchemeModuleInjectiveInternalHomCycleSurjective
import all Linear.SchemeModuleSupportedInternalHomClass
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInjectiveInternalHomCycleMap_surjective
#print axioms LinearStudy.schemeModuleInjectiveInternalHomCycleMap_surjective
#check @LinearStudy.schemeModuleInjectiveInternalHomClassMap_closedDiscrete_surjective
#print axioms LinearStudy.schemeModuleInjectiveInternalHomClassMap_closedDiscrete_surjective
#check @LinearStudy.schemeModuleInjectiveInternalHomClassMap_closedDiscrete_zero_iff
#print axioms LinearStudy.schemeModuleInjectiveInternalHomClassMap_closedDiscrete_zero_iff
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInjectiveInternalHomCycleMap_surjective,true),(`LinearStudy.schemeModuleInjectiveInternalHomClassMap_closedDiscrete_surjective,true),(`LinearStudy.schemeModuleInjectiveInternalHomClassMap_closedDiscrete_zero_iff,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
