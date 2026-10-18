module
import all Linear.CochainResolutionExtSourceSquare
import all Linear.CochainResolutionAugmentationZero
import all Linear.OriginalChainAugmentationClassZero
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.cochainResolutionExtClass_sourceSquare
#print axioms LinearStudy.cochainResolutionExtClass_sourceSquare
#check @LinearStudy.cochainResolutionExtClass_zero
#print axioms LinearStudy.cochainResolutionExtClass_zero
#check @LinearStudy.cochainSingle_positive_shiftedHom_zero
#print axioms LinearStudy.cochainSingle_positive_shiftedHom_zero
#check @LinearStudy.cochainResolutionExtClass_augmentation_precomp_zero
#print axioms LinearStudy.cochainResolutionExtClass_augmentation_precomp_zero
#check @LinearStudy.originalChainAugmentationAsCochain_f_zero
#print axioms LinearStudy.originalChainAugmentationAsCochain_f_zero
#check @LinearStudy.originalChainTopExtClass_augmentation_precomp_zero
#print axioms LinearStudy.originalChainTopExtClass_augmentation_precomp_zero
#check @LinearStudy.originalChainTopExtClass_quotient_precomp_zero
#print axioms LinearStudy.originalChainTopExtClass_quotient_precomp_zero
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.cochainResolutionExtClass_sourceSquare,true),(`LinearStudy.cochainResolutionExtClass_zero,true),(`LinearStudy.cochainSingle_positive_shiftedHom_zero,true),(`LinearStudy.cochainResolutionExtClass_augmentation_precomp_zero,true),(`LinearStudy.originalChainAugmentationAsCochain_f_zero,true),(`LinearStudy.originalChainTopExtClass_augmentation_precomp_zero,true),(`LinearStudy.originalChainTopExtClass_quotient_precomp_zero,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
