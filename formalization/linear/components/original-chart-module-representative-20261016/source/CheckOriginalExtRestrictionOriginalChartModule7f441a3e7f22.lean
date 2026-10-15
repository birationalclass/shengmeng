module
import all Linear.ProjectivePulledOriginalChartModuleExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalChartModuleExtLaw
#print axioms LinearStudy.projectivePulledOriginalChartModuleExtLaw
#check @LinearStudy.projectivePulledOriginalChartModuleExtLaw_proof
#print axioms LinearStudy.projectivePulledOriginalChartModuleExtLaw_proof
#print LinearStudy.projectivePulledOriginalChartModuleExtLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalChartModuleExtLaw,false),(`LinearStudy.projectivePulledOriginalChartModuleExtLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
