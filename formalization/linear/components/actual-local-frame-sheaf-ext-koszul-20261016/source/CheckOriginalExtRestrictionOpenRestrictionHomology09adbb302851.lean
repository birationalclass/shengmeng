module
import all Linear.SchemeModuleOverHomology
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOverFunctor_additive
#print axioms LinearStudy.schemeModuleOverFunctor_additive
#check @LinearStudy.schemeModuleOverFunctor_preservesHomology
#print axioms LinearStudy.schemeModuleOverFunctor_preservesHomology
#check @LinearStudy.schemeModuleOverHomologyIso
#print axioms LinearStudy.schemeModuleOverHomologyIso
#print LinearStudy.schemeModuleOverHomologyIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOverFunctor_additive,true),(`LinearStudy.schemeModuleOverFunctor_preservesHomology,true),(`LinearStudy.schemeModuleOverHomologyIso,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
