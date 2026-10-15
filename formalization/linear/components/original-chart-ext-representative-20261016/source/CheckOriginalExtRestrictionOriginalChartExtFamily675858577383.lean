module
import all Linear.ProjectivePulledOriginalSetupChartExtRepresentativeFamily
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalSetupChartExtRepresentativeFamilyProof
#print axioms LinearStudy.projectivePulledOriginalSetupChartExtRepresentativeFamilyProof
#print LinearStudy.projectivePulledOriginalSetupChartExtRepresentativeFamilyProof
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalSetupChartExtRepresentativeFamilyProof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
