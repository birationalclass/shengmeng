module
import all Linear.SchemeModuleGlobalToInternalExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInjectiveCocycleToInternalExt
#print axioms LinearStudy.schemeModuleInjectiveCocycleToInternalExt
#check @LinearStudy.schemeModuleGlobalToInternalExtViaResolution
#print axioms LinearStudy.schemeModuleGlobalToInternalExtViaResolution
#check @LinearStudy.schemeModuleGlobalToInternalExtViaResolution_extMk
#print axioms LinearStudy.schemeModuleGlobalToInternalExtViaResolution_extMk
#check @LinearStudy.schemeModuleGlobalToInternalExtSectionsViaResolution
#print axioms LinearStudy.schemeModuleGlobalToInternalExtSectionsViaResolution
#print LinearStudy.schemeModuleInjectiveCocycleToInternalExt
#print LinearStudy.schemeModuleGlobalToInternalExtViaResolution
#print LinearStudy.schemeModuleGlobalToInternalExtSectionsViaResolution
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInjectiveCocycleToInternalExt,false),(`LinearStudy.schemeModuleGlobalToInternalExtViaResolution,false),(`LinearStudy.schemeModuleGlobalToInternalExtViaResolution_extMk,true),(`LinearStudy.schemeModuleGlobalToInternalExtSectionsViaResolution,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
