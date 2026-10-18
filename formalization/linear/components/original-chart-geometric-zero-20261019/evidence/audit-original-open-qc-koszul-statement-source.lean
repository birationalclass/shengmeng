module
import all Linear.SchemeModuleOriginalOpenKoszulQCCutStatement
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalOpenKoszulQCCutStatement
#print axioms LinearStudy.schemeModuleOriginalOpenKoszulQCCutStatement
#check @LinearStudy.schemeModuleOriginalOpenKoszulQCCutStatement_proof
#print axioms LinearStudy.schemeModuleOriginalOpenKoszulQCCutStatement_proof
#print LinearStudy.schemeModuleOriginalOpenKoszulQCCutStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalOpenKoszulQCCutStatement,false),(`LinearStudy.schemeModuleOriginalOpenKoszulQCCutStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
