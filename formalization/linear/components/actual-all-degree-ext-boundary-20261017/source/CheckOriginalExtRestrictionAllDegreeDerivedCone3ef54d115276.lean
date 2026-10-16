module
import all Linear.HomCocycleShiftedComposition
import all Linear.CochainConeLiftDerivedAllDegrees
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.actualHomCocycleComp_shiftedHom
#print axioms LinearStudy.actualHomCocycleComp_shiftedHom
#check @LinearStudy.cochainConeLiftDerived_allDegrees
#print axioms LinearStudy.cochainConeLiftDerived_allDegrees
#check @LinearStudy.cochainConeLiftTriangle_allDegrees
#print axioms LinearStudy.cochainConeLiftTriangle_allDegrees
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.actualHomCocycleComp_shiftedHom,true),(`LinearStudy.cochainConeLiftDerived_allDegrees,true),(`LinearStudy.cochainConeLiftTriangle_allDegrees,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
