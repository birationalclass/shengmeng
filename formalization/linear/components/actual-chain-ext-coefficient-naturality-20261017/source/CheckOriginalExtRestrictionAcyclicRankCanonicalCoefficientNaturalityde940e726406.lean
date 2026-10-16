module
import all Linear.SchemeModuleAcyclicRankCanonicalExtCoefficientNaturality
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleAcyclicCokernelRankCanonicalExtIso_coefficientNaturality
#print axioms LinearStudy.schemeModuleAcyclicCokernelRankCanonicalExtIso_coefficientNaturality
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleAcyclicCokernelRankCanonicalExtIso_coefficientNaturality,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
