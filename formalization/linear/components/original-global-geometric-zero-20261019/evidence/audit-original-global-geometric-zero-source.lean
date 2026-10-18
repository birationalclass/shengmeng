module
import all Linear.ProjectivePulledOriginalGlobalGeometricZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalGlobalGeometricZeroStatement
#print axioms LinearStudy.projectivePulledOriginalGlobalGeometricZeroStatement
#check @LinearStudy.projectivePulledOriginalGlobalGeometricZeroStatement_proof
#print axioms LinearStudy.projectivePulledOriginalGlobalGeometricZeroStatement_proof
#print LinearStudy.projectivePulledOriginalGlobalGeometricZeroStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalGlobalGeometricZeroStatement,false),(`LinearStudy.projectivePulledOriginalGlobalGeometricZeroStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
