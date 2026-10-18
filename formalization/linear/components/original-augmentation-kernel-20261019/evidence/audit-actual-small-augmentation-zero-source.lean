module
import all Linear.SchemeModuleOriginalClassAugmentationZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleOriginalSmallClass_augmentation_precomp_zero
#print axioms LinearStudy.schemeModuleOriginalSmallClass_augmentation_precomp_zero
#check @LinearStudy.schemeModuleOriginalSmallClass_quotient_precomp_zero
#print axioms LinearStudy.schemeModuleOriginalSmallClass_quotient_precomp_zero
#check @LinearStudy.schemeModuleOriginalClassAugmentationZeroStatement
#print axioms LinearStudy.schemeModuleOriginalClassAugmentationZeroStatement
#check @LinearStudy.schemeModuleOriginalClassAugmentationZeroStatement_proof
#print axioms LinearStudy.schemeModuleOriginalClassAugmentationZeroStatement_proof
#print LinearStudy.schemeModuleOriginalClassAugmentationZeroStatement
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleOriginalSmallClass_augmentation_precomp_zero,true),(`LinearStudy.schemeModuleOriginalSmallClass_quotient_precomp_zero,true),(`LinearStudy.schemeModuleOriginalClassAugmentationZeroStatement,false),(`LinearStudy.schemeModuleOriginalClassAugmentationZeroStatement_proof,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
