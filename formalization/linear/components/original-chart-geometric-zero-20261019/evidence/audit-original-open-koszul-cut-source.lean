module
import all Linear.SchemeModuleOriginalOpenKoszulCut
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalOpenKoszulCutIso
#print axioms LinearStudy.schemeModuleOriginalOpenKoszulCutIso
#check @LinearStudy.schemeModuleOriginalOpenKoszulCutIso_class
#print axioms LinearStudy.schemeModuleOriginalOpenKoszulCutIso_class
#print LinearStudy.schemeModuleOriginalOpenKoszulCutIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalOpenKoszulCutIso,false),(`LinearStudy.schemeModuleOriginalOpenKoszulCutIso_class,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
