module
import all Linear.ProjectivePulledOriginalExactChartData
import all Linear.ProjectivePulledOriginalNamedExactChart
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalExactChartData
#print axioms LinearStudy.projectivePulledOriginalExactChartData
#check @LinearStudy.projectivePulledOriginalNamedExactChart
#print axioms LinearStudy.projectivePulledOriginalNamedExactChart
#print LinearStudy.projectivePulledOriginalExactChartData
#print LinearStudy.projectivePulledOriginalNamedExactChart
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalExactChartData,false),(`LinearStudy.projectivePulledOriginalNamedExactChart,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
