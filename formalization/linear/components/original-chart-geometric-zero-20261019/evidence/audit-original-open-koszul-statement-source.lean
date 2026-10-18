module
import all Linear.SchemeModuleOriginalOpenKoszulCutStatement
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalOpenKoszulCutStatement
#print axioms LinearStudy.schemeModuleOriginalOpenKoszulCutStatement
#check @LinearStudy.schemeModuleOriginalOpenKoszulCutStatement_proof
#print axioms LinearStudy.schemeModuleOriginalOpenKoszulCutStatement_proof
#print LinearStudy.schemeModuleOriginalOpenKoszulCutStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalOpenKoszulCutStatement,false),(`LinearStudy.schemeModuleOriginalOpenKoszulCutStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
