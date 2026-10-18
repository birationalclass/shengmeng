module
import all Linear.SchemeModuleFlasqueKernelSectionLifting
import all Linear.SchemeModuleSupportedUnitHomLifting
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.moduleSheafGlobalSectionMorphism_of_morphism
#print axioms LinearStudy.moduleSheafGlobalSectionMorphism_of_morphism
#check @LinearStudy.schemeModule_epi_sections_surjective_of_flasqueKernel
#print axioms LinearStudy.schemeModule_epi_sections_surjective_of_flasqueKernel
#check @LinearStudy.schemeModule_unitHom_lift_of_flasqueKernel
#print axioms LinearStudy.schemeModule_unitHom_lift_of_flasqueKernel
#check @LinearStudy.schemeModule_unitHom_lift_of_closedDiscreteSubHom
#print axioms LinearStudy.schemeModule_unitHom_lift_of_closedDiscreteSubHom
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.moduleSheafGlobalSectionMorphism_of_morphism,true),(`LinearStudy.schemeModule_epi_sections_surjective_of_flasqueKernel,true),(`LinearStudy.schemeModule_unitHom_lift_of_flasqueKernel,true),(`LinearStudy.schemeModule_unitHom_lift_of_closedDiscreteSubHom,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
