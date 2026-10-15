module
import all Linear.SchemeModuleHomUnitCurry
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleHomUnitAddEquiv
#print axioms LinearStudy.schemeModuleHomUnitAddEquiv
#check @LinearStudy.schemeModuleHomUnitAddEquiv_symm_postcompose
#print axioms LinearStudy.schemeModuleHomUnitAddEquiv_symm_postcompose
#print LinearStudy.schemeModuleHomUnitAddEquiv
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleHomUnitAddEquiv,false),(`LinearStudy.schemeModuleHomUnitAddEquiv_symm_postcompose,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
