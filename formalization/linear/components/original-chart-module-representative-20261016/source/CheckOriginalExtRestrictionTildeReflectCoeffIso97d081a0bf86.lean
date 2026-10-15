module
import all Linear.TildeReflectsKoszulExact
import all Linear.TildeKoszulCoforkModuleExtIso
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.tilde_chainComplex_exactAt_iff
#print axioms LinearStudy.tilde_chainComplex_exactAt_iff
#check @LinearStudy.tildeKoszul_moduleExact_of_coforkQuasiIso
#print axioms LinearStudy.tildeKoszul_moduleExact_of_coforkQuasiIso
#check @LinearStudy.tildeKoszulIsoCocycle
#print axioms LinearStudy.tildeKoszulIsoCocycle
#check @LinearStudy.tildeKoszulIsoCocycle_isCocycle
#print axioms LinearStudy.tildeKoszulIsoCocycle_isCocycle
#check @LinearStudy.tildeKoszulIsoCocycleModuleExt
#print axioms LinearStudy.tildeKoszulIsoCocycleModuleExt
#check @LinearStudy.tildeKoszulCoforkModuleExtIsoLaw
#print axioms LinearStudy.tildeKoszulCoforkModuleExtIsoLaw
#check @LinearStudy.tildeKoszulCoforkModuleExtIsoLaw_proof
#print axioms LinearStudy.tildeKoszulCoforkModuleExtIsoLaw_proof
#print LinearStudy.tildeKoszulIsoCocycle
#print LinearStudy.tildeKoszulIsoCocycleModuleExt
#print LinearStudy.tildeKoszulCoforkModuleExtIsoLaw
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.tilde_chainComplex_exactAt_iff,true),(`LinearStudy.tildeKoszul_moduleExact_of_coforkQuasiIso,true),(`LinearStudy.tildeKoszulIsoCocycle,false),(`LinearStudy.tildeKoszulIsoCocycle_isCocycle,true),(`LinearStudy.tildeKoszulIsoCocycleModuleExt,false),(`LinearStudy.tildeKoszulCoforkModuleExtIsoLaw,false),(`LinearStudy.tildeKoszulCoforkModuleExtIsoLaw_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
