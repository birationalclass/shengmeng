module
import all Linear.SchemeModuleFlasqueShortExact
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModule_flasque_quotient_of_injective
#print axioms LinearStudy.schemeModule_flasque_quotient_of_injective
#check @LinearStudy.schemeModule_shortExact_unitHom_lift_of_flasque
#print axioms LinearStudy.schemeModule_shortExact_unitHom_lift_of_flasque
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModule_flasque_quotient_of_injective,true),(`LinearStudy.schemeModule_shortExact_unitHom_lift_of_flasque,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
