module
import all Linear.SchemeModuleInjectiveInternalHomNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInjectiveInternalHomCycleMap_i
#print axioms LinearStudy.schemeModuleInjectiveInternalHomCycleMap_i
#check @LinearStudy.schemeModuleInjectiveInternalHomCycleMap_naturality
#print axioms LinearStudy.schemeModuleInjectiveInternalHomCycleMap_naturality
#check @LinearStudy.schemeModuleInjectiveInternalHomClassMap_naturality
#print axioms LinearStudy.schemeModuleInjectiveInternalHomClassMap_naturality
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInjectiveInternalHomCycleMap_i,true),(`LinearStudy.schemeModuleInjectiveInternalHomCycleMap_naturality,true),(`LinearStudy.schemeModuleInjectiveInternalHomClassMap_naturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
