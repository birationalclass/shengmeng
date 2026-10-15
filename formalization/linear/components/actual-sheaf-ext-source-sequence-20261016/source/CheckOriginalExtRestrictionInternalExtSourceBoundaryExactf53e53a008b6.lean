module
import all Linear.SchemeModuleInternalExtSourceBoundaryExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExtSourceMap_comp_boundary
#print axioms LinearStudy.schemeModuleInternalExtSourceMap_comp_boundary
#check @LinearStudy.schemeModuleInternalExtSourceBoundary_comp_map
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundary_comp_map
#check @LinearStudy.schemeModuleInternalExtSourceBoundary_exact_before
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundary_exact_before
#check @LinearStudy.schemeModuleInternalExtSourceBoundary_exact_after
#print axioms LinearStudy.schemeModuleInternalExtSourceBoundary_exact_after
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExtSourceMap_comp_boundary,true),(`LinearStudy.schemeModuleInternalExtSourceBoundary_comp_map,true),(`LinearStudy.schemeModuleInternalExtSourceBoundary_exact_before,true),(`LinearStudy.schemeModuleInternalExtSourceBoundary_exact_after,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
