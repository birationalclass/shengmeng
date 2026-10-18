module
import all Linear.ProjectivePulledOriginalChartDataCutStatement
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalChartDataCutStatement
#print axioms LinearStudy.projectivePulledOriginalChartDataCutStatement
#check @LinearStudy.projectivePulledOriginalChartDataCutStatement_proof
#print axioms LinearStudy.projectivePulledOriginalChartDataCutStatement_proof
#print LinearStudy.projectivePulledOriginalChartDataCutStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalChartDataCutStatement,false),(`LinearStudy.projectivePulledOriginalChartDataCutStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
