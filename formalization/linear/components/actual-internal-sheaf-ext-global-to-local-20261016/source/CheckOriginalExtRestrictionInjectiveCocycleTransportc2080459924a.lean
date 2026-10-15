module
import all Linear.InjectiveCocycleTransport
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.injectiveCocycleTransport
#print axioms LinearStudy.injectiveCocycleTransport
#check @LinearStudy.injectiveCocycleExtMap_transport
#print axioms LinearStudy.injectiveCocycleExtMap_transport
#print LinearStudy.injectiveCocycleTransport
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.injectiveCocycleTransport,false),(`LinearStudy.injectiveCocycleExtMap_transport,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
