module
import all Linear.ProjectivePulledOriginalTopChartModuleFrame
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalTopChartModuleFrame
#print axioms LinearStudy.projectivePulledOriginalTopChartModuleFrame
#check @LinearStudy.projectivePulledOriginalTopChartModuleFrameLaw
#print axioms LinearStudy.projectivePulledOriginalTopChartModuleFrameLaw
#check @LinearStudy.projectivePulledOriginalTopChartModuleFrameLaw_proof
#print axioms LinearStudy.projectivePulledOriginalTopChartModuleFrameLaw_proof
#print LinearStudy.projectivePulledOriginalTopChartModuleFrame
#print LinearStudy.projectivePulledOriginalTopChartModuleFrameLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalTopChartModuleFrame,false),(`LinearStudy.projectivePulledOriginalTopChartModuleFrameLaw,false),(`LinearStudy.projectivePulledOriginalTopChartModuleFrameLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
