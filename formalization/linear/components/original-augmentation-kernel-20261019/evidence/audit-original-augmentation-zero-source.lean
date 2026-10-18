module
import all Linear.ProjectivePulledOriginalAugmentationZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalAugmentationZeroStatement
#print axioms LinearStudy.projectivePulledOriginalAugmentationZeroStatement
#check @LinearStudy.projectivePulledOriginalAugmentationZeroStatement_proof
#print axioms LinearStudy.projectivePulledOriginalAugmentationZeroStatement_proof
#print LinearStudy.projectivePulledOriginalAugmentationZeroStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalAugmentationZeroStatement,false),(`LinearStudy.projectivePulledOriginalAugmentationZeroStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
