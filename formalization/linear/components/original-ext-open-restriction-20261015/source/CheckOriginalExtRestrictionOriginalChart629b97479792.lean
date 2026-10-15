module
import all Linear.ProjectivePulledOriginalWholeCutExtChartRestriction
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalWholeCutExtChartRestrictionProof
#print axioms LinearStudy.projectivePulledOriginalWholeCutExtChartRestrictionProof
#print LinearStudy.projectivePulledOriginalWholeCutExtChartRestrictionProof
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalWholeCutExtChartRestrictionProof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
