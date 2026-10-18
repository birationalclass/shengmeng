-- Reaudit after reusing original existing cycleMap_i;no duplicate new theorem.
module
import all Linear.SchemeModuleClosedDiscreteGlobalToInternalExt
import all Linear.SchemeModuleClosedDiscreteGlobalToInternalExtSections
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleGlobalToInternalExtViaResolution_closedDiscrete_bijective
#print axioms LinearStudy.schemeModuleGlobalToInternalExtViaResolution_closedDiscrete_bijective
#check @LinearStudy.schemeModuleGlobalToInternalExt_closedDiscrete_bijective
#print axioms LinearStudy.schemeModuleGlobalToInternalExt_closedDiscrete_bijective
#check @LinearStudy.schemeModuleGlobalToInternalExt_artinianClosedImmersion_bijective
#print axioms LinearStudy.schemeModuleGlobalToInternalExt_artinianClosedImmersion_bijective
#check @LinearStudy.schemeModuleGlobalToInternalExtSections_closedDiscrete_bijective
#print axioms LinearStudy.schemeModuleGlobalToInternalExtSections_closedDiscrete_bijective
#check @LinearStudy.schemeModuleGlobalToInternalExtSections_artinianClosedImmersion_bijective
#print axioms LinearStudy.schemeModuleGlobalToInternalExtSections_artinianClosedImmersion_bijective
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleGlobalToInternalExtViaResolution_closedDiscrete_bijective,true),(`LinearStudy.schemeModuleGlobalToInternalExt_closedDiscrete_bijective,true),(`LinearStudy.schemeModuleGlobalToInternalExt_artinianClosedImmersion_bijective,true),(`LinearStudy.schemeModuleGlobalToInternalExtSections_closedDiscrete_bijective,true),(`LinearStudy.schemeModuleGlobalToInternalExtSections_artinianClosedImmersion_bijective,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
