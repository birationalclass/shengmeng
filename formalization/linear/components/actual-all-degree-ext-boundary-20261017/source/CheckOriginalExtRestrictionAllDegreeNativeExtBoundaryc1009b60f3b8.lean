module
import all Linear.CochainConeLiftTriangleDegrees
import all Linear.ShortExactInjectiveExtBoundaryAllDegrees
import all Linear.ShortExactInjectiveCocycleAllDegrees
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainConeLiftTriangle_degrees
#print axioms LinearStudy.cochainConeLiftTriangle_degrees
#check @LinearStudy.shortExactInjectiveExtBoundary_allDegrees
#print axioms LinearStudy.shortExactInjectiveExtBoundary_allDegrees
#check @LinearStudy.shortExactInjectiveCocycle_allDegrees_exists
#print axioms LinearStudy.shortExactInjectiveCocycle_allDegrees_exists
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainConeLiftTriangle_degrees,true),(`LinearStudy.shortExactInjectiveExtBoundary_allDegrees,true),(`LinearStudy.shortExactInjectiveCocycle_allDegrees_exists,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
