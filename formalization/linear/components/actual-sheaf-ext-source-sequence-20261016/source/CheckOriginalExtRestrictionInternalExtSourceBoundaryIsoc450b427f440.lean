module
import all Linear.SchemeModuleInternalExtSourceBoundaryIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryIsoViaResolution
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryIsoViaResolution
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryIsoViaResolution_hom
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryIsoViaResolution_hom
#print LinearStudy.schemeModuleInternalExtSourceBoundaryIsoViaResolution
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExtSourceBoundaryIsoViaResolution,false),(`LinearStudy.schemeModuleInternalExtSourceBoundaryIsoViaResolution_hom,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
