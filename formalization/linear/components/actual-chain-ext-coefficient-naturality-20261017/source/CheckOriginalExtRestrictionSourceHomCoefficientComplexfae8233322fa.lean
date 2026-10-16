module
import all Linear.SchemeModuleSourceHomCoefficientComplex
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleSourceHomCoefficientComplexMap
#print axioms LinearStudy.schemeModuleSourceHomCoefficientComplexMap
#check @LinearStudy.schemeModuleSourceHomCoefficientComplexMap_id
#print axioms LinearStudy.schemeModuleSourceHomCoefficientComplexMap_id
#check @LinearStudy.schemeModuleSourceHomCoefficientComplexMap_comp
#print axioms LinearStudy.schemeModuleSourceHomCoefficientComplexMap_comp
#check @LinearStudy.schemeModuleSourceHomCoefficientComplexFunctor
#print axioms LinearStudy.schemeModuleSourceHomCoefficientComplexFunctor
#check @LinearStudy.schemeModuleSourceHomCohomologyFunctor
#print axioms LinearStudy.schemeModuleSourceHomCohomologyFunctor
#check @LinearStudy.schemeModuleSourceHomCohomologyFunctor_map
#print axioms LinearStudy.schemeModuleSourceHomCohomologyFunctor_map
#print LinearStudy.schemeModuleSourceHomCoefficientComplexMap
#print LinearStudy.schemeModuleSourceHomCoefficientComplexFunctor
#print LinearStudy.schemeModuleSourceHomCohomologyFunctor
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleSourceHomCoefficientComplexMap,false),(`LinearStudy.schemeModuleSourceHomCoefficientComplexMap_id,true),(`LinearStudy.schemeModuleSourceHomCoefficientComplexMap_comp,true),(`LinearStudy.schemeModuleSourceHomCoefficientComplexFunctor,false),(`LinearStudy.schemeModuleSourceHomCohomologyFunctor,false),(`LinearStudy.schemeModuleSourceHomCohomologyFunctor_map,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
