module
import all Linear.OriginalForgottenDualMapEvaluation
import all Linear.NativeSpecifiedNormalizationCoefficientPairing
import all Linear.CoextensionEvaluationAtOne
import all Linear.CoextensionNativeTopDualityInputs
import all Linear.NativeCoextensionSpecifiedEvaluationTrace
import all Linear.OriginalGradedCoextensionAdjoint
import all Linear.OriginalGradedCoextensionAdjointZero
import all Linear.NativeCoextensionSpecifiedTraceAdjointPairing
import all Linear.NativeCoextensionSpecifiedTraceLeftSeparation
import all Linear.SchemeModuleActualTraceVanishing
import all Linear.NativeCoextensionSpecifiedTraceHomVanishing
import all Linear.NativeCoextensionSpecifiedTraceAllTwistsVanishing
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.originalForgottenModuleDualMap_apply
#print axioms LinearStudy.originalForgottenModuleDualMap_apply
#check @LinearStudy.originalForgottenLinearDualMap_apply
#print axioms LinearStudy.originalForgottenLinearDualMap_apply
#check @LinearStudy.originalSpecifiedEvaluationPairing_of_coefficientSquare
#print axioms LinearStudy.originalSpecifiedEvaluationPairing_of_coefficientSquare
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientValue
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientValue
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientPairing
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientPairing
#check @LinearStudy.coextensionOriginalEvaluationAtOne
#print axioms LinearStudy.coextensionOriginalEvaluationAtOne
#check @LinearStudy.coextensionOriginalEvaluationAtOne_apply
#print axioms LinearStudy.coextensionOriginalEvaluationAtOne_apply
#check @LinearStudy.coextensionOriginalEvaluationAtOne_mem_integerGradedHomPiece
#print axioms LinearStudy.coextensionOriginalEvaluationAtOne_mem_integerGradedHomPiece
#check @LinearStudy.coextensionOriginalBaseScalarTower
#print axioms LinearStudy.coextensionOriginalBaseScalarTower
#check @LinearStudy.coextensionOriginalTopDualityTorsionFree
#print axioms LinearStudy.coextensionOriginalTopDualityTorsionFree
#check @LinearStudy.coextensionTraceBaseSourceTower
#print axioms LinearStudy.coextensionTraceBaseSourceTower
#check @LinearStudy.coextensionTraceFieldSourceTower
#print axioms LinearStudy.coextensionTraceFieldSourceTower
#check @LinearStudy.coextensionTraceFiniteBase
#print axioms LinearStudy.coextensionTraceFiniteBase
#check @LinearStudy.coextensionTraceFiniteSource
#print axioms LinearStudy.coextensionTraceFiniteSource
#check @LinearStudy.coextensionTraceTorsionFree
#print axioms LinearStudy.coextensionTraceTorsionFree
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationHom
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationHom
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_apply
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_apply
#check @LinearStudy.coextensionOriginalAdjoint
#print axioms LinearStudy.coextensionOriginalAdjoint
#check @LinearStudy.coextensionOriginalAdjoint_apply
#print axioms LinearStudy.coextensionOriginalAdjoint_apply
#check @LinearStudy.coextensionOriginalEvaluationAtOne_adjoint
#print axioms LinearStudy.coextensionOriginalEvaluationAtOne_adjoint
#check @LinearStudy.coextensionOriginalAdjoint_homogeneous
#print axioms LinearStudy.coextensionOriginalAdjoint_homogeneous
#check @LinearStudy.coextensionOriginalAdjoint_degreeZero
#print axioms LinearStudy.coextensionOriginalAdjoint_degreeZero
#check @LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_adjointPairing
#print axioms LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_adjointPairing
#check @LinearStudy.nativeCoextensionSpecifiedTrace_actualHom_left_separates
#print axioms LinearStudy.nativeCoextensionSpecifiedTrace_actualHom_left_separates
#check @LinearStudy.schemeModuleActualTraceSeparation_vanish_of_hom_zero
#print axioms LinearStudy.schemeModuleActualTraceSeparation_vanish_of_hom_zero
#check @LinearStudy.nativeCoextensionSpecifiedTrace_actualTop_vanish_of_hom_zero
#print axioms LinearStudy.nativeCoextensionSpecifiedTrace_actualTop_vanish_of_hom_zero
#check @LinearStudy.nativeCoextensionSpecifiedTrace_actualTop_allTwists_vanish_of_hom_zero
#print axioms LinearStudy.nativeCoextensionSpecifiedTrace_actualTop_allTwists_vanish_of_hom_zero
#print LinearStudy.coextensionOriginalEvaluationAtOne
#print LinearStudy.coextensionOriginalBaseScalarTower
#print LinearStudy.coextensionOriginalTopDualityTorsionFree
#print LinearStudy.coextensionTraceBaseSourceTower
#print LinearStudy.coextensionTraceFieldSourceTower
#print LinearStudy.coextensionTraceFiniteBase
#print LinearStudy.coextensionTraceFiniteSource
#print LinearStudy.coextensionTraceTorsionFree
#print LinearStudy.nativeCoextensionSpecifiedTopEvaluationHom
#print LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace
#print LinearStudy.coextensionOriginalAdjoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.originalForgottenModuleDualMap_apply,true),(`LinearStudy.originalForgottenLinearDualMap_apply,true),(`LinearStudy.originalSpecifiedEvaluationPairing_of_coefficientSquare,true),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientValue,true),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficientPairing,true),(`LinearStudy.coextensionOriginalEvaluationAtOne,false),(`LinearStudy.coextensionOriginalEvaluationAtOne_apply,true),(`LinearStudy.coextensionOriginalEvaluationAtOne_mem_integerGradedHomPiece,true),(`LinearStudy.coextensionOriginalBaseScalarTower,true),(`LinearStudy.coextensionOriginalTopDualityTorsionFree,true),(`LinearStudy.coextensionTraceBaseSourceTower,true),(`LinearStudy.coextensionTraceFieldSourceTower,true),(`LinearStudy.coextensionTraceFiniteBase,true),(`LinearStudy.coextensionTraceFiniteSource,true),(`LinearStudy.coextensionTraceTorsionFree,true),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationHom,false),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace,false),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_apply,true),(`LinearStudy.coextensionOriginalAdjoint,false),(`LinearStudy.coextensionOriginalAdjoint_apply,true),(`LinearStudy.coextensionOriginalEvaluationAtOne_adjoint,true),(`LinearStudy.coextensionOriginalAdjoint_homogeneous,true),(`LinearStudy.coextensionOriginalAdjoint_degreeZero,true),(`LinearStudy.nativeCoextensionSpecifiedTopEvaluationTrace_adjointPairing,true),(`LinearStudy.nativeCoextensionSpecifiedTrace_actualHom_left_separates,true),(`LinearStudy.schemeModuleActualTraceSeparation_vanish_of_hom_zero,true),(`LinearStudy.nativeCoextensionSpecifiedTrace_actualTop_vanish_of_hom_zero,true),(`LinearStudy.nativeCoextensionSpecifiedTrace_actualTop_allTwists_vanish_of_hom_zero,true)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
    let kernelKind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | _ => "other"
    unless kernelKind == (if want then "theorem" else "definition") do
      throwError m!"Incorrect kernel declaration kind: {n}"
    Lean.logInfo m!"KINDCHECK:{n}:{kernelKind}"
