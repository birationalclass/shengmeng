module
import all Linear.SchemeModuleInjectiveHomExact
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleInjectiveInternalHom_preservesEpimorphisms
#print axioms LinearStudy.schemeModuleInjectiveInternalHom_preservesEpimorphisms
#check @LinearStudy.schemeModuleInjectiveInternalHom_preservesHomology
#print axioms LinearStudy.schemeModuleInjectiveInternalHom_preservesHomology
#check @LinearStudy.schemeModuleInjectiveInternalHom_preservesFiniteColimits
#print axioms LinearStudy.schemeModuleInjectiveInternalHom_preservesFiniteColimits
#check @LinearStudy.schemeModuleInjectiveHomAugmentationMap
#print axioms LinearStudy.schemeModuleInjectiveHomAugmentationMap
#check @LinearStudy.schemeModuleInjectiveHomAugmentationMap_quasiIso
#print axioms LinearStudy.schemeModuleInjectiveHomAugmentationMap_quasiIso
#check @LinearStudy.schemeModuleInjectiveHomAugmentationMap_f
#print axioms LinearStudy.schemeModuleInjectiveHomAugmentationMap_f
#print LinearStudy.schemeModuleInjectiveHomAugmentationMap
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleInjectiveInternalHom_preservesEpimorphisms,true),(`LinearStudy.schemeModuleInjectiveInternalHom_preservesHomology,true),(`LinearStudy.schemeModuleInjectiveInternalHom_preservesFiniteColimits,true),(`LinearStudy.schemeModuleInjectiveHomAugmentationMap,false),(`LinearStudy.schemeModuleInjectiveHomAugmentationMap_quasiIso,true),(`LinearStudy.schemeModuleInjectiveHomAugmentationMap_f,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
