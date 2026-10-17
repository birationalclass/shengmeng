module
import all Linear.SchemeModuleInjectiveCocycleEvaluation
import all Linear.SchemeModuleInjectiveCocycleBoundary
import all Linear.SchemeModuleGlobalToInternalExtBoundary
import all Linear.SchemeModuleCanonicalGlobalToInternalExtBoundary
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInjectiveCocycleToInternalExt_apply
#print axioms LinearStudy.schemeModuleInjectiveCocycleToInternalExt_apply
#check @LinearStudy.schemeModuleInjectiveCocycleToInternalExt_boundary
#print axioms LinearStudy.schemeModuleInjectiveCocycleToInternalExt_boundary
#check @LinearStudy.schemeModuleGlobalToInternalExtViaResolution_boundary
#print axioms LinearStudy.schemeModuleGlobalToInternalExtViaResolution_boundary
#check @LinearStudy.schemeModuleGlobalToInternalExt_boundary
#print axioms LinearStudy.schemeModuleGlobalToInternalExt_boundary
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInjectiveCocycleToInternalExt_apply,true),(`LinearStudy.schemeModuleInjectiveCocycleToInternalExt_boundary,true),(`LinearStudy.schemeModuleGlobalToInternalExtViaResolution_boundary,true),(`LinearStudy.schemeModuleGlobalToInternalExt_boundary,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
