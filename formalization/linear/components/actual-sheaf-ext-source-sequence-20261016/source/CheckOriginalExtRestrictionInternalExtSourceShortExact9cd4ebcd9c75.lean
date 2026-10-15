module
import all Linear.SchemeModuleInternalHomSourceShortExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomCoefficientComplex
#print axioms LinearStudy.schemeModuleHomCoefficientComplex
#check @LinearStudy.schemeModuleHomCoefficientComplexMap
#print axioms LinearStudy.schemeModuleHomCoefficientComplexMap
#check @LinearStudy.schemeModuleHomPrecompose_zero
#print axioms LinearStudy.schemeModuleHomPrecompose_zero
#check @LinearStudy.schemeModuleHomSourceShortComplex
#print axioms LinearStudy.schemeModuleHomSourceShortComplex
#check @LinearStudy.schemeModuleHomSourceShortComplex_shortExact
#print axioms LinearStudy.schemeModuleHomSourceShortComplex_shortExact
#check @LinearStudy.schemeModuleHomCoefficientComplexMap_f
#print axioms LinearStudy.schemeModuleHomCoefficientComplexMap_f
#print LinearStudy.schemeModuleHomCoefficientComplex
#print LinearStudy.schemeModuleHomCoefficientComplexMap
#print LinearStudy.schemeModuleHomSourceShortComplex
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomCoefficientComplex,false),(`LinearStudy.schemeModuleHomCoefficientComplexMap,false),(`LinearStudy.schemeModuleHomPrecompose_zero,true),(`LinearStudy.schemeModuleHomSourceShortComplex,false),(`LinearStudy.schemeModuleHomSourceShortComplex_shortExact,true),(`LinearStudy.schemeModuleHomCoefficientComplexMap_f,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
