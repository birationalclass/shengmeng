module
import all Linear.ExtCovariantComplexSerreBound
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.extCovariantComplex_middle_from_Serre_bound
#print axioms LinearStudy.extCovariantComplex_middle_from_Serre_bound
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.extCovariantComplex_middle_from_Serre_bound,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
