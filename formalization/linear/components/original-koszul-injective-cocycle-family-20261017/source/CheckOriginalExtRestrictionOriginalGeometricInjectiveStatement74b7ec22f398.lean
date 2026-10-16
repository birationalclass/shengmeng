module
import all Linear.ProjectivePulledOriginalWholeCutInjectiveStatement
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalWholeCutInjectiveStatement
#print axioms LinearStudy.projectivePulledOriginalWholeCutInjectiveStatement
#check @LinearStudy.projectivePulledOriginalWholeCutInjectiveStatement_proof
#print axioms LinearStudy.projectivePulledOriginalWholeCutInjectiveStatement_proof
#print LinearStudy.projectivePulledOriginalWholeCutInjectiveStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalWholeCutInjectiveStatement,false),(`LinearStudy.projectivePulledOriginalWholeCutInjectiveStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
