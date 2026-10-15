module
import all Linear.TildeActualCocycleModuleExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.tildeActualFunctionalPreimage
#print axioms LinearStudy.tildeActualFunctionalPreimage
#check @LinearStudy.tildeActualFunctionalPreimage_map
#print axioms LinearStudy.tildeActualFunctionalPreimage_map
#check @LinearStudy.tildeActualFunctionalPreimage_isCocycle
#print axioms LinearStudy.tildeActualFunctionalPreimage_isCocycle
#check @LinearStudy.tildeActualCocycleModuleExt
#print axioms LinearStudy.tildeActualCocycleModuleExt
#check @LinearStudy.tildeActualCocycleModuleExtLaw
#print axioms LinearStudy.tildeActualCocycleModuleExtLaw
#check @LinearStudy.tildeActualCocycleModuleExtLaw_proof
#print axioms LinearStudy.tildeActualCocycleModuleExtLaw_proof
#print LinearStudy.tildeActualFunctionalPreimage
#print LinearStudy.tildeActualCocycleModuleExt
#print LinearStudy.tildeActualCocycleModuleExtLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.tildeActualFunctionalPreimage,false),(`LinearStudy.tildeActualFunctionalPreimage_map,true),(`LinearStudy.tildeActualFunctionalPreimage_isCocycle,true),(`LinearStudy.tildeActualCocycleModuleExt,false),(`LinearStudy.tildeActualCocycleModuleExtLaw,false),(`LinearStudy.tildeActualCocycleModuleExtLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
