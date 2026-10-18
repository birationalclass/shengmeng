module
import all Linear.ProjectivePulledOriginalChartDataCutZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalChartDataCutZeroStatement
#print axioms LinearStudy.projectivePulledOriginalChartDataCutZeroStatement
#check @LinearStudy.projectivePulledOriginalChartDataCutZeroStatement_proof
#print axioms LinearStudy.projectivePulledOriginalChartDataCutZeroStatement_proof
#print LinearStudy.projectivePulledOriginalChartDataCutZeroStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalChartDataCutZeroStatement,false),(`LinearStudy.projectivePulledOriginalChartDataCutZeroStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
