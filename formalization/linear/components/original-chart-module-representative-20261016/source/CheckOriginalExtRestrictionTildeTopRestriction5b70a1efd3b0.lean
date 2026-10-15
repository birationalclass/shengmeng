module
import all Linear.TildeActualModuleExtTopRestriction
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.tildeActualCocycleModuleExt_topRestriction
#print axioms LinearStudy.tildeActualCocycleModuleExt_topRestriction
#check @LinearStudy.tildeKoszulIsoCocycleModuleExt_topRestriction
#print axioms LinearStudy.tildeKoszulIsoCocycleModuleExt_topRestriction
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.tildeActualCocycleModuleExt_topRestriction,true),(`LinearStudy.tildeKoszulIsoCocycleModuleExt_topRestriction,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
