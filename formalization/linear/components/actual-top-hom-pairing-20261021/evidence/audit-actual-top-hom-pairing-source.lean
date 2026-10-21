module
import all Linear.NativeFiniteNormalizationActualTopDuality
import all Linear.OriginalNormalizationActualTopDuality
import all Linear.ActualAdditiveDualPairing
import all Linear.NativeFiniteNormalizationActualPairing
import all Linear.OriginalNormalizationActualPairing
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.nativeFiniteNormalization_actualTopHomDualIso
#print axioms LinearStudy.nativeFiniteNormalization_actualTopHomDualIso
#check @LinearStudy.originalNormalization_actualTopHomDualIso
#print axioms LinearStudy.originalNormalization_actualTopHomDualIso
#check @LinearStudy.actualAbelianIsoAddEquiv
#print axioms LinearStudy.actualAbelianIsoAddEquiv
#check @LinearStudy.additiveDualComparisonPairing
#print axioms LinearStudy.additiveDualComparisonPairing
#check @LinearStudy.additiveDualComparisonPairing_left_nondegenerate
#print axioms LinearStudy.additiveDualComparisonPairing_left_nondegenerate
#check @LinearStudy.additiveDualComparisonPairing_right_nondegenerate
#print axioms LinearStudy.additiveDualComparisonPairing_right_nondegenerate
#check @LinearStudy.nativeFiniteNormalizationActualTopPairing
#print axioms LinearStudy.nativeFiniteNormalizationActualTopPairing
#check @LinearStudy.nativeFiniteNormalizationActualTopPairing_apply
#print axioms LinearStudy.nativeFiniteNormalizationActualTopPairing_apply
#check @LinearStudy.nativeFiniteNormalizationActualTopPairing_left_nondegenerate
#print axioms LinearStudy.nativeFiniteNormalizationActualTopPairing_left_nondegenerate
#check @LinearStudy.nativeFiniteNormalizationActualTopPairing_right_nondegenerate
#print axioms LinearStudy.nativeFiniteNormalizationActualTopPairing_right_nondegenerate
#check @LinearStudy.originalNormalizationActualTopHomPairing
#print axioms LinearStudy.originalNormalizationActualTopHomPairing
#print LinearStudy.nativeFiniteNormalization_actualTopHomDualIso
#print LinearStudy.originalNormalization_actualTopHomDualIso
#print LinearStudy.actualAbelianIsoAddEquiv
#print LinearStudy.additiveDualComparisonPairing
#print LinearStudy.nativeFiniteNormalizationActualTopPairing
#print LinearStudy.originalNormalizationActualTopHomPairing
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.nativeFiniteNormalization_actualTopHomDualIso,false),(`LinearStudy.originalNormalization_actualTopHomDualIso,false),(`LinearStudy.actualAbelianIsoAddEquiv,false),(`LinearStudy.additiveDualComparisonPairing,false),(`LinearStudy.additiveDualComparisonPairing_left_nondegenerate,true),(`LinearStudy.additiveDualComparisonPairing_right_nondegenerate,true),(`LinearStudy.nativeFiniteNormalizationActualTopPairing,false),(`LinearStudy.nativeFiniteNormalizationActualTopPairing_apply,true),(`LinearStudy.nativeFiniteNormalizationActualTopPairing_left_nondegenerate,true),(`LinearStudy.nativeFiniteNormalizationActualTopPairing_right_nondegenerate,true),(`LinearStudy.originalNormalizationActualTopHomPairing,false)]
  let env ← Lean.getEnv
  for (n,want) in checks do
    let some info := env.find? n | throwError "Missing declaration"
    unless (← Lean.Meta.isProp info.type) == want do
      throwError m!"Incorrect semantic proof role: {n}"
    Lean.logInfo m!"ROLECHECK:{n}:{want}"
