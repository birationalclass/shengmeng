module
import all Linear.ProjectivePulledOriginalChartAugmentationLaw
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalChartAugmentationLaw
#print axioms LinearStudy.projectivePulledOriginalChartAugmentationLaw
#check @LinearStudy.projectivePulledOriginalChartAugmentationLaw_proof
#print axioms LinearStudy.projectivePulledOriginalChartAugmentationLaw_proof
#print LinearStudy.projectivePulledOriginalChartAugmentationLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalChartAugmentationLaw,false),(`LinearStudy.projectivePulledOriginalChartAugmentationLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
