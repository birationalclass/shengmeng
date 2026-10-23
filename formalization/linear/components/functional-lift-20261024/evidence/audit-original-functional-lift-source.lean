module
import all Linear.SchemeModuleExtTracePairing
import all Linear.SchemeModuleActualTraceCalibration
import all Linear.NativeCoextensionSpecifiedGlobalExtTrace
import all Linear.IntegerGradedHomPieceFinite
import all Linear.FiniteAdditiveDualRepresentative
import all Linear.NativeCoextensionSpecifiedFunctionalLift
import all Linear.NativeCoextensionSpecifiedLinearFunctionalLift
import all Linear.SchemeModuleActualTraceRepresentingNonzero
import all Linear.NativeCoextensionSpecifiedNonzeroFunctionalLift
import all Linear.NativeCoextensionOriginalBoundaryFunctionalLift
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @LinearStudy.schemeModuleActualHTracePairing
#print axioms LinearStudy.schemeModuleActualHTracePairing
#check @LinearStudy.schemeModuleExtSectionTracePairing
#print axioms LinearStudy.schemeModuleExtSectionTracePairing
#check @LinearStudy.schemeModuleExtClassCoefficientPushforwardAddHom
#print axioms LinearStudy.schemeModuleExtClassCoefficientPushforwardAddHom
#check @LinearStudy.schemeModuleExtClassActualSectionBoundary_trace_transpose
#print axioms LinearStudy.schemeModuleExtClassActualSectionBoundary_trace_transpose
#check @LinearStudy.schemeModuleOriginalActualSectionBoundary_trace_transpose
#print axioms LinearStudy.schemeModuleOriginalActualSectionBoundary_trace_transpose
#check @LinearStudy.schemeModuleExtClassCoefficientPushforward_injective_of_trace
#print axioms LinearStudy.schemeModuleExtClassCoefficientPushforward_injective_of_trace
#check @LinearStudy.schemeModuleActualHToGlobalExtTrace
#print axioms LinearStudy.schemeModuleActualHToGlobalExtTrace
#check @LinearStudy.schemeModuleActualHToGlobalExtTrace_pairing
#print axioms LinearStudy.schemeModuleActualHToGlobalExtTrace_pairing
#check @LinearStudy.schemeModuleOriginalActualSectionBoundary_actualH_trace_transpose
#print axioms LinearStudy.schemeModuleOriginalActualSectionBoundary_actualH_trace_transpose
#check @LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace
#print axioms LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace
#check @LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace_apply
#print axioms LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace_apply
#check @LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace_actualPairing
#print axioms LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace_actualPairing
#check @LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace_originalBoundary
#print axioms LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace_originalBoundary
#check @LinearStudy.integerGradedHomPiece_finite_of_pieces
#print axioms LinearStudy.integerGradedHomPiece_finite_of_pieces
#check @LinearStudy.polynomialIntegerPiece_finite
#print axioms LinearStudy.polynomialIntegerPiece_finite
#check @LinearStudy.polynomialIntegerGradedHomPiece_finite
#print axioms LinearStudy.polynomialIntegerGradedHomPiece_finite
#check @LinearStudy.finiteAdditiveDual_exists_representative
#print axioms LinearStudy.finiteAdditiveDual_exists_representative
#check @LinearStudy.nativeCoextensionSpecifiedTrace_exists_functional_lift_of_originalScalar
#print axioms LinearStudy.nativeCoextensionSpecifiedTrace_exists_functional_lift_of_originalScalar
#check @LinearStudy.nativeCoextensionSpecifiedTrace_exists_linear_functional_lift
#print axioms LinearStudy.nativeCoextensionSpecifiedTrace_exists_linear_functional_lift
#check @LinearStudy.schemeModuleActualTraceRepresentingMap_ne_zero
#print axioms LinearStudy.schemeModuleActualTraceRepresentingMap_ne_zero
#check @LinearStudy.nativeCoextensionSpecifiedTrace_exists_nonzero_functional_lift_of_originalScalar
#print axioms LinearStudy.nativeCoextensionSpecifiedTrace_exists_nonzero_functional_lift_of_originalScalar
#check @LinearStudy.nativeCoextensionSpecifiedTrace_exists_nonzero_original_boundary_representative
#print axioms LinearStudy.nativeCoextensionSpecifiedTrace_exists_nonzero_original_boundary_representative
#print LinearStudy.schemeModuleActualHTracePairing
#print LinearStudy.schemeModuleExtSectionTracePairing
#print LinearStudy.schemeModuleExtClassCoefficientPushforwardAddHom
#print LinearStudy.schemeModuleActualHToGlobalExtTrace
#print LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`LinearStudy.schemeModuleActualHTracePairing,false),(`LinearStudy.schemeModuleExtSectionTracePairing,false),(`LinearStudy.schemeModuleExtClassCoefficientPushforwardAddHom,false),(`LinearStudy.schemeModuleExtClassActualSectionBoundary_trace_transpose,true),(`LinearStudy.schemeModuleOriginalActualSectionBoundary_trace_transpose,true),(`LinearStudy.schemeModuleExtClassCoefficientPushforward_injective_of_trace,true),(`LinearStudy.schemeModuleActualHToGlobalExtTrace,false),(`LinearStudy.schemeModuleActualHToGlobalExtTrace_pairing,true),(`LinearStudy.schemeModuleOriginalActualSectionBoundary_actualH_trace_transpose,true),(`LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace,false),(`LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace_apply,true),(`LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace_actualPairing,true),(`LinearStudy.nativeCoextensionSpecifiedTopGlobalExtTrace_originalBoundary,true),(`LinearStudy.integerGradedHomPiece_finite_of_pieces,true),(`LinearStudy.polynomialIntegerPiece_finite,true),(`LinearStudy.polynomialIntegerGradedHomPiece_finite,true),(`LinearStudy.finiteAdditiveDual_exists_representative,true),(`LinearStudy.nativeCoextensionSpecifiedTrace_exists_functional_lift_of_originalScalar,true),(`LinearStudy.nativeCoextensionSpecifiedTrace_exists_linear_functional_lift,true),(`LinearStudy.schemeModuleActualTraceRepresentingMap_ne_zero,true),(`LinearStudy.nativeCoextensionSpecifiedTrace_exists_nonzero_functional_lift_of_originalScalar,true),(`LinearStudy.nativeCoextensionSpecifiedTrace_exists_nonzero_original_boundary_representative,true)]
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
