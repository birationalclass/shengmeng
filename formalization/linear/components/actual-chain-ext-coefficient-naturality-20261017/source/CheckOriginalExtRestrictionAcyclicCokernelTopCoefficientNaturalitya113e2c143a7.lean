module
import all Linear.SchemeModuleAcyclicCokernelTopExtCoefficientNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso_coefficientNaturality
#print axioms LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso_coefficientNaturality
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleAcyclicCokernelTopInternalExtIso_coefficientNaturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
