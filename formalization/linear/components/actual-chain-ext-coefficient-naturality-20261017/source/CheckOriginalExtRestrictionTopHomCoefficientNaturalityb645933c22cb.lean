module
import all Linear.SchemeModuleTopHomCoefficientNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChainDifferentialHomCokernelCoefficientMap
#print axioms LinearStudy.schemeModuleChainDifferentialHomCokernelCoefficientMap
#check @LinearStudy.schemeModuleChainDifferentialHomCokernelCoefficientMap_projection
#print axioms LinearStudy.schemeModuleChainDifferentialHomCokernelCoefficientMap_projection
#check @LinearStudy.schemeModuleChainTopHomCokernelIso_coefficientNaturality
#print axioms LinearStudy.schemeModuleChainTopHomCokernelIso_coefficientNaturality
#check @LinearStudy.schemeModuleSourceHomHomologyIsoSc_coefficientNaturality
#print axioms LinearStudy.schemeModuleSourceHomHomologyIsoSc_coefficientNaturality
#print LinearStudy.schemeModuleChainDifferentialHomCokernelCoefficientMap
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChainDifferentialHomCokernelCoefficientMap,false),(`LinearStudy.schemeModuleChainDifferentialHomCokernelCoefficientMap_projection,true),(`LinearStudy.schemeModuleChainTopHomCokernelIso_coefficientNaturality,true),(`LinearStudy.schemeModuleSourceHomHomologyIsoSc_coefficientNaturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
