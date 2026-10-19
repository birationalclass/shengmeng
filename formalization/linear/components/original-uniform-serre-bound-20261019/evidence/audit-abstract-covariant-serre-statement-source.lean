module
import all Linear.SchemeModuleOriginalCovariantSerreStatement
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalCovariantSerreStatement
#print axioms LinearStudy.schemeModuleOriginalCovariantSerreStatement
#check @LinearStudy.schemeModuleOriginalCovariantSerreStatement_proof
#print axioms LinearStudy.schemeModuleOriginalCovariantSerreStatement_proof
#print LinearStudy.schemeModuleOriginalCovariantSerreStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalCovariantSerreStatement,false),(`LinearStudy.schemeModuleOriginalCovariantSerreStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
