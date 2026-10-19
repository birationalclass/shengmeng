module
import all Linear.ProjectivePulledOriginalCovariantExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.projectivePulledOriginalCovariantExactStatement
#print axioms LinearStudy.projectivePulledOriginalCovariantExactStatement
#check @LinearStudy.projectivePulledOriginalCovariantExactStatement_proof
#print axioms LinearStudy.projectivePulledOriginalCovariantExactStatement_proof
#print LinearStudy.projectivePulledOriginalCovariantExactStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.projectivePulledOriginalCovariantExactStatement,false),(`LinearStudy.projectivePulledOriginalCovariantExactStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
