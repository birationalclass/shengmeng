module
import all Linear.SchemeModuleIteratedShiftCoefficientNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleChainOpcycleIteratedExtIso_coefficientNaturality
#print axioms LinearStudy.schemeModuleChainOpcycleIteratedExtIso_coefficientNaturality
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleChainOpcycleIteratedExtIso_coefficientNaturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
