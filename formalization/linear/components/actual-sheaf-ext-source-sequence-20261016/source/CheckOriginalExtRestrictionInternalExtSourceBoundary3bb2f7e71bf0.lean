module
import all Linear.SchemeModuleInternalExtSourceBoundary
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution
#check @LinearStudy.schemeModuleInternalExtSourceBoundary_resolution_square
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundary_resolution_square
#print LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExtSourceBoundaryViaResolution,false),(`LinearStudy.schemeModuleInternalExtSourceBoundary_resolution_square,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
