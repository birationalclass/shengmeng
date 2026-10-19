module
import all Linear.FormalCoproductFunctorMap
import all Linear.CoverGeneratedTerminalPresheaf
import all Linear.FormalCechYonedaAdjunction
import all Linear.FormalCechFormalEvaluation
import all Linear.FormalCechSimplicialResolution
import all Linear.AugmentedAlternatingWhiskering
import all Linear.AugmentedPointwiseWhiskering
import all Linear.FormalCechPresheafResolution
import all Linear.TopCoverGeneratedTerminalSheaf
import all Linear.TopCechIntegerTarget
import all Linear.TopCechFreeSheafResolution
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @CategoryTheory.Functor.mapFormalCoproduct
#print axioms CategoryTheory.Functor.mapFormalCoproduct
#check @CategoryTheory.Subfunctor.ofObjects
#print axioms CategoryTheory.Subfunctor.ofObjects
#check @CategoryTheory.Subfunctor.ofObjects_obj_eq_univ
#print axioms CategoryTheory.Subfunctor.ofObjects_obj_eq_univ
#check @CategoryTheory.Subfunctor.ofObjects_obj_eq_empty
#print axioms CategoryTheory.Subfunctor.ofObjects_obj_eq_empty
#check @CategoryTheory.Subfunctor.uniqueOfObjectsObj
#print axioms CategoryTheory.Subfunctor.uniqueOfObjectsObj
#check @CategoryTheory.Subfunctor.isTerminalOfObjectsToFunctor
#print axioms CategoryTheory.Subfunctor.isTerminalOfObjectsToFunctor
#check @CategoryTheory.isTerminalShrinkYonedaObj
#print axioms CategoryTheory.isTerminalShrinkYonedaObj
#check @CategoryTheory.Subfunctor.ofObjectsIsoOfAdj
#print axioms CategoryTheory.Subfunctor.ofObjectsIsoOfAdj
#check @CategoryTheory.Adjunction.shrinkYonedaIso
#print axioms CategoryTheory.Adjunction.shrinkYonedaIso
#check @CategoryTheory.Limits.FormalCoproduct.evalObjCompIso
#print axioms CategoryTheory.Limits.FormalCoproduct.evalObjCompIso
#check @CategoryTheory.Limits.FormalCoproduct.evalShrinkYonedaCompIsoOfAdj
#print axioms CategoryTheory.Limits.FormalCoproduct.evalShrinkYonedaCompIsoOfAdj
#check @CategoryTheory.Limits.FormalCoproduct.mapFormalCoproductObjPowerIso
#print axioms CategoryTheory.Limits.FormalCoproduct.mapFormalCoproductObjPowerIso
#check @CategoryTheory.Limits.FormalCoproduct.cechCompMapFormalCoproductIso
#print axioms CategoryTheory.Limits.FormalCoproduct.cechCompMapFormalCoproductIso
#check @CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCech
#print axioms CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCech
#check @CategoryTheory.Limits.FormalCoproduct.isEmpty_shrinkYonedaCechRightObj
#print axioms CategoryTheory.Limits.FormalCoproduct.isEmpty_shrinkYonedaCechRightObj
#check @CategoryTheory.Limits.FormalCoproduct.extraDegeneracyShrinkYonedaCech
#print axioms CategoryTheory.Limits.FormalCoproduct.extraDegeneracyShrinkYonedaCech
#check @CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCechIsoOfAdj
#print axioms CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCechIsoOfAdj
#check @CategoryTheory.Limits.FormalCoproduct.nonempty_extraDegeneracy_shrinkYonedaCech_evaluation
#print axioms CategoryTheory.Limits.FormalCoproduct.nonempty_extraDegeneracy_shrinkYonedaCech_evaluation
#check @LinearStudy.alternatingAugmentationWhiskeringArrowIso
#print axioms LinearStudy.alternatingAugmentationWhiskeringArrowIso
#check @LinearStudy.augmentedPointwiseWhiskeringIso
#print axioms LinearStudy.augmentedPointwiseWhiskeringIso
#check @CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCech_presheaf_augmentation_quasiIso
#print axioms CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCech_presheaf_augmentation_quasiIso
#check @LinearStudy.topCoverGeneratedTerminal_locallySurjective
#print axioms LinearStudy.topCoverGeneratedTerminal_locallySurjective
#check @LinearStudy.topCoverGeneratedTerminal_locallyInjective
#print axioms LinearStudy.topCoverGeneratedTerminal_locallyInjective
#check @LinearStudy.topCoverGeneratedTerminal_sheafify_inclusion_isIso
#print axioms LinearStudy.topCoverGeneratedTerminal_sheafify_inclusion_isIso
#check @LinearStudy.topCoverGeneratedTerminal_freeAbelian_sheafify_inclusion_isIso
#print axioms LinearStudy.topCoverGeneratedTerminal_freeAbelian_sheafify_inclusion_isIso
#check @LinearStudy.freePUnitNativeIntegerIso
#print axioms LinearStudy.freePUnitNativeIntegerIso
#check @LinearStudy.topCoverGeneratedFreeAbelianIntegerTargetMap
#print axioms LinearStudy.topCoverGeneratedFreeAbelianIntegerTargetMap
#check @LinearStudy.topCoverGeneratedFreeAbelianIntegerTargetMap_isIso
#print axioms LinearStudy.topCoverGeneratedFreeAbelianIntegerTargetMap_isIso
#check @LinearStudy.topCechFreeAbelianAugmented
#print axioms LinearStudy.topCechFreeAbelianAugmented
#check @LinearStudy.topCechFreeAbelianAugmented_quasiIso
#print axioms LinearStudy.topCechFreeAbelianAugmented_quasiIso
#check @LinearStudy.topCechNativeIntegerAugmentation
#print axioms LinearStudy.topCechNativeIntegerAugmentation
#check @LinearStudy.topCechNativeIntegerAugmentation_quasiIso
#print axioms LinearStudy.topCechNativeIntegerAugmentation_quasiIso
#print CategoryTheory.Functor.mapFormalCoproduct
#print CategoryTheory.Subfunctor.ofObjects
#print CategoryTheory.Subfunctor.uniqueOfObjectsObj
#print CategoryTheory.Subfunctor.isTerminalOfObjectsToFunctor
#print CategoryTheory.isTerminalShrinkYonedaObj
#print CategoryTheory.Subfunctor.ofObjectsIsoOfAdj
#print CategoryTheory.Adjunction.shrinkYonedaIso
#print CategoryTheory.Limits.FormalCoproduct.evalObjCompIso
#print CategoryTheory.Limits.FormalCoproduct.evalShrinkYonedaCompIsoOfAdj
#print CategoryTheory.Limits.FormalCoproduct.mapFormalCoproductObjPowerIso
#print CategoryTheory.Limits.FormalCoproduct.cechCompMapFormalCoproductIso
#print CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCech
#print CategoryTheory.Limits.FormalCoproduct.extraDegeneracyShrinkYonedaCech
#print CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCechIsoOfAdj
#print LinearStudy.alternatingAugmentationWhiskeringArrowIso
#print LinearStudy.augmentedPointwiseWhiskeringIso
#print LinearStudy.freePUnitNativeIntegerIso
#print LinearStudy.topCoverGeneratedFreeAbelianIntegerTargetMap
#print LinearStudy.topCechFreeAbelianAugmented
#print LinearStudy.topCechNativeIntegerAugmentation
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`CategoryTheory.Functor.mapFormalCoproduct,false),(`CategoryTheory.Subfunctor.ofObjects,false),(`CategoryTheory.Subfunctor.ofObjects_obj_eq_univ,true),(`CategoryTheory.Subfunctor.ofObjects_obj_eq_empty,true),(`CategoryTheory.Subfunctor.uniqueOfObjectsObj,false),(`CategoryTheory.Subfunctor.isTerminalOfObjectsToFunctor,false),(`CategoryTheory.isTerminalShrinkYonedaObj,false),(`CategoryTheory.Subfunctor.ofObjectsIsoOfAdj,false),(`CategoryTheory.Adjunction.shrinkYonedaIso,false),(`CategoryTheory.Limits.FormalCoproduct.evalObjCompIso,false),(`CategoryTheory.Limits.FormalCoproduct.evalShrinkYonedaCompIsoOfAdj,false),(`CategoryTheory.Limits.FormalCoproduct.mapFormalCoproductObjPowerIso,false),(`CategoryTheory.Limits.FormalCoproduct.cechCompMapFormalCoproductIso,false),(`CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCech,false),(`CategoryTheory.Limits.FormalCoproduct.isEmpty_shrinkYonedaCechRightObj,true),(`CategoryTheory.Limits.FormalCoproduct.extraDegeneracyShrinkYonedaCech,false),(`CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCechIsoOfAdj,false),(`CategoryTheory.Limits.FormalCoproduct.nonempty_extraDegeneracy_shrinkYonedaCech_evaluation,true),(`LinearStudy.alternatingAugmentationWhiskeringArrowIso,false),(`LinearStudy.augmentedPointwiseWhiskeringIso,false),(`CategoryTheory.Limits.FormalCoproduct.shrinkYonedaCech_presheaf_augmentation_quasiIso,true),(`LinearStudy.topCoverGeneratedTerminal_locallySurjective,true),(`LinearStudy.topCoverGeneratedTerminal_locallyInjective,true),(`LinearStudy.topCoverGeneratedTerminal_sheafify_inclusion_isIso,true),(`LinearStudy.topCoverGeneratedTerminal_freeAbelian_sheafify_inclusion_isIso,true),(`LinearStudy.freePUnitNativeIntegerIso,false),(`LinearStudy.topCoverGeneratedFreeAbelianIntegerTargetMap,false),(`LinearStudy.topCoverGeneratedFreeAbelianIntegerTargetMap_isIso,true),(`LinearStudy.topCechFreeAbelianAugmented,false),(`LinearStudy.topCechFreeAbelianAugmented_quasiIso,true),(`LinearStudy.topCechNativeIntegerAugmentation,false),(`LinearStudy.topCechNativeIntegerAugmentation_quasiIso,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
