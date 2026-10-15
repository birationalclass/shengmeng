module
import all Linear.SchemeModuleHomPostcomposeSection
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomPostcomposeSection
#print axioms LinearStudy.schemeModuleHomPostcomposeSection
#check @LinearStudy.schemeModuleHomPostcomposeSection_evaluation
#print axioms LinearStudy.schemeModuleHomPostcomposeSection_evaluation
#print LinearStudy.schemeModuleHomPostcomposeSection
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomPostcomposeSection,false),(`LinearStudy.schemeModuleHomPostcomposeSection_evaluation,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
