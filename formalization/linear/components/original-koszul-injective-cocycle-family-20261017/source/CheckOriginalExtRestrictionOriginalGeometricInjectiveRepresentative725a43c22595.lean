module
import all Linear.ProjectivePulledOriginalWholeCutInjectiveCocycle
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalWholeCutInjectiveCocycleProof
#print axioms LinearStudy.projectivePulledOriginalWholeCutInjectiveCocycleProof
#print LinearStudy.projectivePulledOriginalWholeCutInjectiveCocycleProof
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalWholeCutInjectiveCocycleProof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
