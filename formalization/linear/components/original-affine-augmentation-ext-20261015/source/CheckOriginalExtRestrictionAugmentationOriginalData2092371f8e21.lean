module
import all Linear.ProjectivePulledOriginalChartPresentation
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalChartPresentationData
#print axioms LinearStudy.projectivePulledOriginalChartPresentationData
#check @LinearStudy.projectivePulledOriginalChartPresentationData_source
#print axioms LinearStudy.projectivePulledOriginalChartPresentationData_source
#print LinearStudy.projectivePulledOriginalChartPresentationData
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalChartPresentationData,false),(`LinearStudy.projectivePulledOriginalChartPresentationData_source,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
