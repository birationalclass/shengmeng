module
import all Linear.TopOpenFreeAbelianSheaf
import all Linear.TopOpenFreeAbelianSheafSections
import all Linear.TopOpenFreeAbelianSheafSectionsNaturality
import all Linear.TopAbelianSheafInjectiveFlasque
import all Linear.TopAbelianSheafIntegerSections
import all Linear.TopAbelianSheafFlasqueShortExact
import all Linear.TopAbelianSheafFlasqueCohomology
import all Linear.SchemeModuleInjectiveActualCohomology
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.topOpenFreeAbelianPresheafFunctor
#print axioms LinearStudy.topOpenFreeAbelianPresheafFunctor
#check @LinearStudy.topOpenFreeAbelianPresheaf_map_mono
#print axioms LinearStudy.topOpenFreeAbelianPresheaf_map_mono
#check @LinearStudy.topOpenFreeAbelianSheafFunctor
#print axioms LinearStudy.topOpenFreeAbelianSheafFunctor
#check @LinearStudy.topOpenFreeAbelianSheaf_map_mono
#print axioms LinearStudy.topOpenFreeAbelianSheaf_map_mono
#check @LinearStudy.topOpenFreeAbelianSheafHomEquiv
#print axioms LinearStudy.topOpenFreeAbelianSheafHomEquiv
#check @LinearStudy.topOpenFreeAbelianSheafHomEquiv_restrict
#print axioms LinearStudy.topOpenFreeAbelianSheafHomEquiv_restrict
#check @LinearStudy.topOpenFreeAbelianSheafHomEquiv_postcompose
#print axioms LinearStudy.topOpenFreeAbelianSheafHomEquiv_postcompose
#check @LinearStudy.topAbelianSheaf_injective_isFlasque
#print axioms LinearStudy.topAbelianSheaf_injective_isFlasque
#check @LinearStudy.topAbelianSheafIntegerHomSectionsAddEquiv
#print axioms LinearStudy.topAbelianSheafIntegerHomSectionsAddEquiv
#check @LinearStudy.topAbelianSheafIntegerHomSectionsAddEquiv_postcompose
#print axioms LinearStudy.topAbelianSheafIntegerHomSectionsAddEquiv_postcompose
#check @LinearStudy.topAbelianSheaf_flasque_quotient_of_injective
#print axioms LinearStudy.topAbelianSheaf_flasque_quotient_of_injective
#check @LinearStudy.topAbelianSheaf_shortExact_integerHom_lift_of_flasque
#print axioms LinearStudy.topAbelianSheaf_shortExact_integerHom_lift_of_flasque
#check @LinearStudy.topAbelianSheaf_flasque_higherCohomology_vanish
#print axioms LinearStudy.topAbelianSheaf_flasque_higherCohomology_vanish
#check @LinearStudy.schemeModule_injective_actualHigherCohomology_vanish
#print axioms LinearStudy.schemeModule_injective_actualHigherCohomology_vanish
#print LinearStudy.topOpenFreeAbelianPresheafFunctor
#print LinearStudy.topOpenFreeAbelianSheafFunctor
#print LinearStudy.topOpenFreeAbelianSheafHomEquiv
#print LinearStudy.topAbelianSheafIntegerHomSectionsAddEquiv
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.topOpenFreeAbelianPresheafFunctor,false),(`LinearStudy.topOpenFreeAbelianPresheaf_map_mono,true),(`LinearStudy.topOpenFreeAbelianSheafFunctor,false),(`LinearStudy.topOpenFreeAbelianSheaf_map_mono,true),(`LinearStudy.topOpenFreeAbelianSheafHomEquiv,false),(`LinearStudy.topOpenFreeAbelianSheafHomEquiv_restrict,true),(`LinearStudy.topOpenFreeAbelianSheafHomEquiv_postcompose,true),(`LinearStudy.topAbelianSheaf_injective_isFlasque,true),(`LinearStudy.topAbelianSheafIntegerHomSectionsAddEquiv,false),(`LinearStudy.topAbelianSheafIntegerHomSectionsAddEquiv_postcompose,true),(`LinearStudy.topAbelianSheaf_flasque_quotient_of_injective,true),(`LinearStudy.topAbelianSheaf_shortExact_integerHom_lift_of_flasque,true),(`LinearStudy.topAbelianSheaf_flasque_higherCohomology_vanish,true),(`LinearStudy.schemeModule_injective_actualHigherCohomology_vanish,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
