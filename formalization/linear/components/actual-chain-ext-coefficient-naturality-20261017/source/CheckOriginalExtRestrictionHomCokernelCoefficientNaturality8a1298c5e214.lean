module
import all Linear.SchemeModuleHomCokernelCoefficientNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomSourceCokernelCoefficientMap
#print axioms LinearStudy.schemeModuleHomSourceCokernelCoefficientMap
#check @LinearStudy.schemeModuleHomSourceCokernelCoefficientMap_projection
#print axioms LinearStudy.schemeModuleHomSourceCokernelCoefficientMap_projection
#check @LinearStudy.schemeModuleHomSourceBoundaryCokernelIso_coefficientNaturality
#print axioms LinearStudy.schemeModuleHomSourceBoundaryCokernelIso_coefficientNaturality
#print LinearStudy.schemeModuleHomSourceCokernelCoefficientMap
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomSourceCokernelCoefficientMap,false),(`LinearStudy.schemeModuleHomSourceCokernelCoefficientMap_projection,true),(`LinearStudy.schemeModuleHomSourceBoundaryCokernelIso_coefficientNaturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
