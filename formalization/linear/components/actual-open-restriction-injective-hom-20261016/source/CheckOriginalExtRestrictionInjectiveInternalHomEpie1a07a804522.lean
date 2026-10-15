module
import all Linear.SchemeModuleInjectiveHomEpi
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomPrecompose_app_surjective
#print axioms LinearStudy.schemeModuleHomPrecompose_app_surjective
#check @LinearStudy.schemeModuleHomPrecompose_epi
#print axioms LinearStudy.schemeModuleHomPrecompose_epi
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomPrecompose_app_surjective,true),(`LinearStudy.schemeModuleHomPrecompose_epi,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
