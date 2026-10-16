module
import all Linear.CochainConeLiftTriangleEquation
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainConeLiftTriangleEquation
#print axioms LinearStudy.cochainConeLiftTriangleEquation
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainConeLiftTriangleEquation,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
