module
import all Linear.SchemeModuleInternalExtSourceBoundaryNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomSourceShortComplexMap
#print axioms LinearStudy.schemeModuleHomSourceShortComplexMap
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution_naturality
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution_naturality
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution_independent
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution_independent
#check @LinearStudy.schemeModuleInternalExtSourceBoundary
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundary
#check @LinearStudy.schemeModuleInternalExtSourceBoundary_eq_viaResolution
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundary_eq_viaResolution
#print LinearStudy.schemeModuleHomSourceShortComplexMap
#print LinearStudy.schemeModuleInternalExtSourceBoundary
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomSourceShortComplexMap,false),(`LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution_naturality,true),(`LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution_independent,true),(`LinearStudy.schemeModuleInternalExtSourceBoundary,false),(`LinearStudy.schemeModuleInternalExtSourceBoundary_eq_viaResolution,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
