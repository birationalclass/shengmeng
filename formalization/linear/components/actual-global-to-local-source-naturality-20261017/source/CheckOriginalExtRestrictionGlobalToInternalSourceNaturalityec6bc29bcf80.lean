module
import all Linear.SchemeModuleGlobalToInternalExtSourceNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleGlobalToInternalExtViaResolution_sourceNaturality
#print axioms LinearStudy.schemeModuleGlobalToInternalExtViaResolution_sourceNaturality
#check @LinearStudy.schemeModuleGlobalToInternalExt_sourceNaturality
#print axioms LinearStudy.schemeModuleGlobalToInternalExt_sourceNaturality
#check @LinearStudy.schemeModuleGlobalToInternalExtSections_sourceNaturality
#print axioms LinearStudy.schemeModuleGlobalToInternalExtSections_sourceNaturality
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleGlobalToInternalExtViaResolution_sourceNaturality,true),(`LinearStudy.schemeModuleGlobalToInternalExt_sourceNaturality,true),(`LinearStudy.schemeModuleGlobalToInternalExtSections_sourceNaturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
