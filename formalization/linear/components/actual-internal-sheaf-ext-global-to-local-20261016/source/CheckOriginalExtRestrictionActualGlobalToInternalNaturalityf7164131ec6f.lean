module
import all Linear.SchemeModuleGlobalToInternalExtNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInjectiveCocycleToInternalExt_naturality
#print axioms LinearStudy.schemeModuleInjectiveCocycleToInternalExt_naturality
#check @LinearStudy.schemeModuleGlobalToInternalExtViaResolution_naturality
#print axioms LinearStudy.schemeModuleGlobalToInternalExtViaResolution_naturality
#check @LinearStudy.schemeModuleGlobalToInternalExtViaResolution_independent
#print axioms LinearStudy.schemeModuleGlobalToInternalExtViaResolution_independent
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInjectiveCocycleToInternalExt_naturality,true),(`LinearStudy.schemeModuleGlobalToInternalExtViaResolution_naturality,true),(`LinearStudy.schemeModuleGlobalToInternalExtViaResolution_independent,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
