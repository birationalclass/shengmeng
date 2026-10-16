module
import all Linear.SchemeModuleExtIndexCoefficientNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInternalExtSourceIndex_coefficientNaturality
#print axioms LinearStudy.schemeModuleInternalExtSourceIndex_coefficientNaturality
#check @LinearStudy.schemeModuleInternalExtDegree_coefficientNaturality
#print axioms LinearStudy.schemeModuleInternalExtDegree_coefficientNaturality
#check @LinearStudy.schemeModuleSourceHomCohomologyDegree_coefficientNaturality
#print axioms LinearStudy.schemeModuleSourceHomCohomologyDegree_coefficientNaturality
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInternalExtSourceIndex_coefficientNaturality,true),(`LinearStudy.schemeModuleInternalExtDegree_coefficientNaturality,true),(`LinearStudy.schemeModuleSourceHomCohomologyDegree_coefficientNaturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
