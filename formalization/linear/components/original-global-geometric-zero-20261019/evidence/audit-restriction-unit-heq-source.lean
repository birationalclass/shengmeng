module
import all Linear.SchemeModuleRestrictionUnitHEq
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModule_restrictionUnit_isIso_of_chartHEq
#print axioms LinearStudy.schemeModule_restrictionUnit_isIso_of_chartHEq
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModule_restrictionUnit_isIso_of_chartHEq,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
