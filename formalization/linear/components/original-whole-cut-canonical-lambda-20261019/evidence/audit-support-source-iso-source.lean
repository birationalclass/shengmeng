module
import all Linear.SchemeModuleFiniteSupportLambdaSourceIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleGlobalToInternalExt_bijective_of_sourceIso
#print axioms LinearStudy.schemeModuleGlobalToInternalExt_bijective_of_sourceIso
#check @LinearStudy.schemeModuleGlobalToInternalExt_closedDiscrete_bijective_of_sourceIso
#print axioms LinearStudy.schemeModuleGlobalToInternalExt_closedDiscrete_bijective_of_sourceIso
#check @LinearStudy.schemeModuleGlobalToInternalExt_artinianClosed_bijective_of_sourceIso
#print axioms LinearStudy.schemeModuleGlobalToInternalExt_artinianClosed_bijective_of_sourceIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleGlobalToInternalExt_bijective_of_sourceIso,true),(`LinearStudy.schemeModuleGlobalToInternalExt_closedDiscrete_bijective_of_sourceIso,true),(`LinearStudy.schemeModuleGlobalToInternalExt_artinianClosed_bijective_of_sourceIso,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
