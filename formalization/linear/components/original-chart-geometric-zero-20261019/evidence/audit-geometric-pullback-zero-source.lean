module
import all Linear.SchemeModuleGeometricPullbackZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModule_pullback_map_zero_iff_unit
#print axioms LinearStudy.schemeModule_pullback_map_zero_iff_unit
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModule_pullback_map_zero_iff_unit,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
