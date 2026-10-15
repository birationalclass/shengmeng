module
import all Linear.ProjectivePulledOriginalChartExtRepresentative
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalChartExtRepresentativeLaw
#print axioms LinearStudy.projectivePulledOriginalChartExtRepresentativeLaw
#check @LinearStudy.projectivePulledOriginalChartExtRepresentativeLaw_proof
#print axioms LinearStudy.projectivePulledOriginalChartExtRepresentativeLaw_proof
#print LinearStudy.projectivePulledOriginalChartExtRepresentativeLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalChartExtRepresentativeLaw,false),(`LinearStudy.projectivePulledOriginalChartExtRepresentativeLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
