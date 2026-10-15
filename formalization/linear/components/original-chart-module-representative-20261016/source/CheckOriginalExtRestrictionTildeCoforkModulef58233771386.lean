module
import all Linear.TildeKoszulCoforkActualModuleExt
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.tildeKoszulCoforkAugmentation_quasiIso_of_exact
#print axioms LinearStudy.tildeKoszulCoforkAugmentation_quasiIso_of_exact
#check @LinearStudy.tildeKoszulCoforkActualCocycleModuleExtLaw
#print axioms LinearStudy.tildeKoszulCoforkActualCocycleModuleExtLaw
#check @LinearStudy.tildeKoszulCoforkActualCocycleModuleExtLaw_proof
#print axioms LinearStudy.tildeKoszulCoforkActualCocycleModuleExtLaw_proof
#print LinearStudy.tildeKoszulCoforkActualCocycleModuleExtLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.tildeKoszulCoforkAugmentation_quasiIso_of_exact,true),(`LinearStudy.tildeKoszulCoforkActualCocycleModuleExtLaw,false),(`LinearStudy.tildeKoszulCoforkActualCocycleModuleExtLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
