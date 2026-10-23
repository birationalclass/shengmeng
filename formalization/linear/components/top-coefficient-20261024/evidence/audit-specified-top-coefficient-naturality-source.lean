module
import all Linear.IntegerFinitePresentationCoordinateNaturality
import all Linear.SpecifiedDualityCoefficientTransfer
import all Linear.CoordinateCechCoefficientForgettingIdentity
import all Linear.NativeSpecifiedNormalizationTopDualityCoefficient
set_option maxHeartbeats 50000
set_option pp.deepTerms true
set_option pp.funBinderTypes true
#check @MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso_naturality
#print axioms MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso_naturality
#check @LinearStudy.originalSpecifiedDualityCoefficientSquare_of_comparisonSquares
#print axioms LinearStudy.originalSpecifiedDualityCoefficientSquare_of_comparisonSquares
#check @MvPolynomial.coordinateNativeCechHomologyFunctor_map_forget
#print axioms MvPolynomial.coordinateNativeCechHomologyFunctor_map_forget
#check @LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficient
#print axioms LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficient
run_cmd Lean.Elab.Command.liftTermElabM do
  let checks : List (Lean.Name × Bool) := [(`MvPolynomial.coordinateNativeFiniteIntegerPresentationDataGradedHomDualIso_naturality,true),(`LinearStudy.originalSpecifiedDualityCoefficientSquare_of_comparisonSquares,true),(`MvPolynomial.coordinateNativeCechHomologyFunctor_map_forget,true),(`LinearStudy.nativeFiniteNormalization_specifiedActualTopHomDualIso_coefficient,true)]
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
