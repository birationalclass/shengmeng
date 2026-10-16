module
import all Linear.ShortExactInjectiveCochainLiftAllDegrees
import all Linear.CochainConeLiftClassAllDegrees
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.shortExactInjectiveCochainLift_allDegrees_exists
#print axioms LinearStudy.shortExactInjectiveCochainLift_allDegrees_exists
#check @LinearStudy.actualHomCocycleComp
#print axioms LinearStudy.actualHomCocycleComp
#check @LinearStudy.cochainConeLiftClass_allDegrees
#print axioms LinearStudy.cochainConeLiftClass_allDegrees
#print LinearStudy.actualHomCocycleComp
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.shortExactInjectiveCochainLift_allDegrees_exists,true),(`LinearStudy.actualHomCocycleComp,false),(`LinearStudy.cochainConeLiftClass_allDegrees,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
