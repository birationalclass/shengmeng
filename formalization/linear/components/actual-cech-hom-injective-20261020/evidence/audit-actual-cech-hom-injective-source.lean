module
import all Linear.TopOpenFreeAbelianSheafAddSections
import all Linear.TopOpenFreeAbelianHomPresheaf
import all Linear.FormalCoproductContravariantEvaluation
import all Linear.TopFreePresheafHomSheafCoefficient
import all Linear.TopCechFreePresheafSimplicialIso
import all Linear.TopCechFreeSheafHomComplex
import all Linear.AlternatingHomOppositeComplex
import all Linear.InjectiveHomResolutionAcyclic
import all Linear.TopInjectiveAbelianSheafCechAcyclic
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.topOpenFreeAbelianSheafHomSectionsAddEquiv
#print axioms LinearStudy.topOpenFreeAbelianSheafHomSectionsAddEquiv
#check @LinearStudy.topOpenFreeAbelianSheafHomPresheafIso
#print axioms LinearStudy.topOpenFreeAbelianSheafHomPresheafIso
#check @LinearStudy.formalCoproductContravariantComponentIso
#print axioms LinearStudy.formalCoproductContravariantComponentIso
#check @LinearStudy.formalCoproductContravariantComponentIso_hom_π
#print axioms LinearStudy.formalCoproductContravariantComponentIso_hom_π
#check @LinearStudy.formalCoproductContravariantEvaluationIso
#print axioms LinearStudy.formalCoproductContravariantEvaluationIso
#check @LinearStudy.nativeAdjunctionHomPresheafIso
#print axioms LinearStudy.nativeAdjunctionHomPresheafIso
#check @LinearStudy.topOpenFreeAbelianPresheafHomPresheafIso
#print axioms LinearStudy.topOpenFreeAbelianPresheafHomPresheafIso
#check @LinearStudy.topCechFreeAbelianPresheafAugmented
#print axioms LinearStudy.topCechFreeAbelianPresheafAugmented
#check @LinearStudy.topCechFreePresheafSimplicialIso
#print axioms LinearStudy.topCechFreePresheafSimplicialIso
#check @LinearStudy.nativeRightOpIso
#print axioms LinearStudy.nativeRightOpIso
#check @LinearStudy.topCechFreeSheafHomCosimplicialIso
#print axioms LinearStudy.topCechFreeSheafHomCosimplicialIso
#check @LinearStudy.topCechFreeSheafHomComplex
#print axioms LinearStudy.topCechFreeSheafHomComplex
#check @LinearStudy.topCechFreeSheafHomComplexIso
#print axioms LinearStudy.topCechFreeSheafHomComplexIso
#check @LinearStudy.alternatingHomCochainIso
#print axioms LinearStudy.alternatingHomCochainIso
#check @LinearStudy.injectiveHomOppositeOfResolution_exactAt
#print axioms LinearStudy.injectiveHomOppositeOfResolution_exactAt
#check @LinearStudy.topInjectiveAbelianSheaf_nativeCech_exactAt
#print axioms LinearStudy.topInjectiveAbelianSheaf_nativeCech_exactAt
#check @LinearStudy.topInjectiveAbelianSheaf_nativeCech_positiveHomology_isZero
#print axioms LinearStudy.topInjectiveAbelianSheaf_nativeCech_positiveHomology_isZero
#print LinearStudy.topOpenFreeAbelianSheafHomSectionsAddEquiv
#print LinearStudy.topOpenFreeAbelianSheafHomPresheafIso
#print LinearStudy.formalCoproductContravariantComponentIso
#print LinearStudy.formalCoproductContravariantEvaluationIso
#print LinearStudy.nativeAdjunctionHomPresheafIso
#print LinearStudy.topOpenFreeAbelianPresheafHomPresheafIso
#print LinearStudy.topCechFreeAbelianPresheafAugmented
#print LinearStudy.topCechFreePresheafSimplicialIso
#print LinearStudy.nativeRightOpIso
#print LinearStudy.topCechFreeSheafHomCosimplicialIso
#print LinearStudy.topCechFreeSheafHomComplex
#print LinearStudy.topCechFreeSheafHomComplexIso
#print LinearStudy.alternatingHomCochainIso
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.topOpenFreeAbelianSheafHomSectionsAddEquiv,false),(`LinearStudy.topOpenFreeAbelianSheafHomPresheafIso,false),(`LinearStudy.formalCoproductContravariantComponentIso,false),(`LinearStudy.formalCoproductContravariantComponentIso_hom_π,true),(`LinearStudy.formalCoproductContravariantEvaluationIso,false),(`LinearStudy.nativeAdjunctionHomPresheafIso,false),(`LinearStudy.topOpenFreeAbelianPresheafHomPresheafIso,false),(`LinearStudy.topCechFreeAbelianPresheafAugmented,false),(`LinearStudy.topCechFreePresheafSimplicialIso,false),(`LinearStudy.nativeRightOpIso,false),(`LinearStudy.topCechFreeSheafHomCosimplicialIso,false),(`LinearStudy.topCechFreeSheafHomComplex,false),(`LinearStudy.topCechFreeSheafHomComplexIso,false),(`LinearStudy.alternatingHomCochainIso,false),(`LinearStudy.injectiveHomOppositeOfResolution_exactAt,true),(`LinearStudy.topInjectiveAbelianSheaf_nativeCech_exactAt,true),(`LinearStudy.topInjectiveAbelianSheaf_nativeCech_positiveHomology_isZero,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
