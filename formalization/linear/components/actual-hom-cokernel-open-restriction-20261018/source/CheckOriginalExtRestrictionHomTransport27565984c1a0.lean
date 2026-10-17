module
import all Linear.SchemeModuleHomTransportIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomTransportIso
#print axioms LinearStudy.schemeModuleHomTransportIso
#check @LinearStudy.schemeModuleHomTransportIso_hom
#print axioms LinearStudy.schemeModuleHomTransportIso_hom
#check @LinearStudy.schemeModuleHomTransportIso_curry
#print axioms LinearStudy.schemeModuleHomTransportIso_curry
#check @LinearStudy.schemeModuleHomTransportIso_differential
#print axioms LinearStudy.schemeModuleHomTransportIso_differential
#print LinearStudy.schemeModuleHomTransportIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomTransportIso,false),(`LinearStudy.schemeModuleHomTransportIso_hom,true),(`LinearStudy.schemeModuleHomTransportIso_curry,true),(`LinearStudy.schemeModuleHomTransportIso_differential,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
