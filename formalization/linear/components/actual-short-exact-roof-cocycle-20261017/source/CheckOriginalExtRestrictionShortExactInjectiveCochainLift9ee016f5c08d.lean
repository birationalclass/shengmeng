module
import all Linear.ShortExactInjectiveCochainLift
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.shortExactInjectiveCochainLift_exists
#print axioms LinearStudy.shortExactInjectiveCochainLift_exists
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.shortExactInjectiveCochainLift_exists,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
