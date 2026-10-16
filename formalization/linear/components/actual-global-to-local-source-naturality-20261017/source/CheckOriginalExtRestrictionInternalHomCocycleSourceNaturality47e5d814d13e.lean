module
import all Linear.SchemeModuleInjectiveInternalHomSourceNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInjectiveInternalHomCycleMap_sourceNaturality
#print axioms LinearStudy.schemeModuleInjectiveInternalHomCycleMap_sourceNaturality
#check @LinearStudy.schemeModuleInjectiveInternalHomClassMap_sourceNaturality
#print axioms LinearStudy.schemeModuleInjectiveInternalHomClassMap_sourceNaturality
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInjectiveInternalHomCycleMap_sourceNaturality,true),(`LinearStudy.schemeModuleInjectiveInternalHomClassMap_sourceNaturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
