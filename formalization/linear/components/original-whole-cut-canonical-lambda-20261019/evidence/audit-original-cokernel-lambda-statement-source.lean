module
import all Linear.ProjectivePulledWholeCokernelLambdaStatement
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalCokernelLambdaStatement
#print axioms LinearStudy.projectivePulledOriginalCokernelLambdaStatement
#check @LinearStudy.projectivePulledOriginalCokernelLambdaStatement_proof
#print axioms LinearStudy.projectivePulledOriginalCokernelLambdaStatement_proof
#print LinearStudy.projectivePulledOriginalCokernelLambdaStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalCokernelLambdaStatement,false),(`LinearStudy.projectivePulledOriginalCokernelLambdaStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
