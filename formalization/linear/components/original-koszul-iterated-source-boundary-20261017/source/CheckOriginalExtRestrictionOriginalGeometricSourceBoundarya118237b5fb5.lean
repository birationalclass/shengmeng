module
import all Linear.ProjectivePulledOriginalWholeCutSourceBoundaryStatement
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalWholeCutSourceBoundaryStatement
#print axioms LinearStudy.projectivePulledOriginalWholeCutSourceBoundaryStatement
#check @LinearStudy.projectivePulledOriginalWholeCutSourceBoundaryStatement_proof
#print axioms LinearStudy.projectivePulledOriginalWholeCutSourceBoundaryStatement_proof
#print LinearStudy.projectivePulledOriginalWholeCutSourceBoundaryStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalWholeCutSourceBoundaryStatement,false),(`LinearStudy.projectivePulledOriginalWholeCutSourceBoundaryStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
