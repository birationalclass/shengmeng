module
import all Linear.SchemeModuleInternalExtSourceMap
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExtSourceMap
#print axioms LinearStudy.schemeModuleInternalExtSourceMap
#check @LinearStudy.schemeModuleInternalExtSourceMap_id
#print axioms LinearStudy.schemeModuleInternalExtSourceMap_id
#check @LinearStudy.schemeModuleInternalExtSourceMap_comp
#print axioms LinearStudy.schemeModuleInternalExtSourceMap_comp
#check @LinearStudy.schemeModuleInternalExtSourceMap_resolution
#print axioms LinearStudy.schemeModuleInternalExtSourceMap_resolution
#check @LinearStudy.schemeModuleInternalExtSourceMap_resolution_square
#print axioms LinearStudy.schemeModuleInternalExtSourceMap_resolution_square
#check @LinearStudy.schemeModuleHomCoefficientComplexMap_zero
#print axioms LinearStudy.schemeModuleHomCoefficientComplexMap_zero
#check @LinearStudy.schemeModuleInternalExtSourceMap_zero
#print axioms LinearStudy.schemeModuleInternalExtSourceMap_zero
#print LinearStudy.schemeModuleInternalExtSourceMap
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExtSourceMap,false),(`LinearStudy.schemeModuleInternalExtSourceMap_id,true),(`LinearStudy.schemeModuleInternalExtSourceMap_comp,true),(`LinearStudy.schemeModuleInternalExtSourceMap_resolution,true),(`LinearStudy.schemeModuleInternalExtSourceMap_resolution_square,true),(`LinearStudy.schemeModuleHomCoefficientComplexMap_zero,true),(`LinearStudy.schemeModuleInternalExtSourceMap_zero,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
